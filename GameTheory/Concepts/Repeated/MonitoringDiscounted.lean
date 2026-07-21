/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Repeated.MonitoringInstances
import GameTheory.Concepts.Welfare.FolkTheorem.Discounting

/-!
# Discounted Repeated Games with Public Monitoring

Normalized discounted payoffs and perfect-public equilibrium for the realized
public-signal model.  Continuations use `PublicMonitoring.after`, so sequential
rationality is required after every public history, including zero-probability
histories.

The payoff definitions are total for every real discount factor.  Quantitative
results state the standard side conditions `0 ≤ δ` and `δ < 1` explicitly.
-/

noncomputable section

namespace GameTheory

namespace KernelGame

namespace PublicMonitoring

variable {ι : Type} {G : KernelGame ι}

/-- Normalized discounted expected payoff under public monitoring. -/
def discountedAveragePayoff (M : G.PublicMonitoring) (δ : ℝ)
    (σ : M.MonitoredProfile) (who : ι) : ℝ :=
  (1 - δ) * ∑' t : ℕ, δ ^ t * M.stageEU σ t who

/-- Discounted continuation payoff after a specified public history. -/
def discountedContinuationPayoff (M : G.PublicMonitoring) (δ : ℝ)
    (σ : M.MonitoredProfile) {t : ℕ} (h : M.SignalHistory t)
    (who : ι) : ℝ :=
  M.discountedAveragePayoff δ (M.after σ h) who

/-- Discounted monitored stage payoffs are summable when they are uniformly
bounded and the discount factor lies in `[0,1)`. -/
theorem summable_discounted_stageEU_of_abs_bound
    (M : G.PublicMonitoring) {δ C : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {σ : M.MonitoredProfile}
    (who : ι) (hbd : ∀ t, |M.stageEU σ t who| ≤ C) :
    Summable fun t : ℕ => δ ^ t * M.stageEU σ t who := by
  have hgeom : Summable fun t : ℕ => C * δ ^ t :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_left C
  refine Summable.of_norm_bounded hgeom ?_
  intro t
  rw [Real.norm_eq_abs]
  calc
    |δ ^ t * M.stageEU σ t who| =
        δ ^ t * |M.stageEU σ t who| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
    _ ≤ δ ^ t * C :=
      mul_le_mul_of_nonneg_left (hbd t) (pow_nonneg hδ0 t)
    _ = C * δ ^ t := by ring

/-- Pointwise dominance of monitored stage payoffs implies dominance of their
normalized discounted payoffs. -/
theorem discountedAveragePayoff_le_of_forall_stageEU_le
    (M : G.PublicMonitoring) {δ C : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ τ : M.MonitoredProfile} (who : ι)
    (hbdσ : ∀ t, |M.stageEU σ t who| ≤ C)
    (hbdτ : ∀ t, |M.stageEU τ t who| ≤ C)
    (hle : ∀ t, M.stageEU σ t who ≤ M.stageEU τ t who) :
    M.discountedAveragePayoff δ σ who ≤
      M.discountedAveragePayoff δ τ who := by
  have hsσ := M.summable_discounted_stageEU_of_abs_bound hδ0 hδ1 who hbdσ
  have hsτ := M.summable_discounted_stageEU_of_abs_bound hδ0 hδ1 who hbdτ
  have hsum :
      (∑' t : ℕ, δ ^ t * M.stageEU σ t who) ≤
        ∑' t : ℕ, δ ^ t * M.stageEU τ t who := by
    exact hsσ.tsum_le_tsum
      (fun t => mul_le_mul_of_nonneg_left (hle t) (pow_nonneg hδ0 t)) hsτ
  exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hδ1.le)

/-- Discounted payoff of stationary monitored play equals its stage payoff. -/
@[simp] theorem discountedAveragePayoff_stationaryMonitoredProfile
    (M : G.PublicMonitoring) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (σ : Profile G) (who : ι) :
    M.discountedAveragePayoff δ (M.stationaryMonitoredProfile σ) who =
      G.eu σ who := by
  have hne : 1 - δ ≠ 0 := by linarith
  simp [discountedAveragePayoff, tsum_mul_right,
    tsum_geometric_of_lt_one hδ0 hδ1, hne]

/-- `ε`-Nash equilibrium of the discounted repeated game in public
strategies. -/
def IsεDiscountedPublicNash (M : G.PublicMonitoring) [DecidableEq ι]
    (δ ε : ℝ) (σ : M.MonitoredProfile) : Prop :=
  ∀ who (dev : M.MonitoredStrategy who),
    M.discountedAveragePayoff δ σ who + ε ≥
      M.discountedAveragePayoff δ (Function.update σ who dev) who

/-- Exact Nash equilibrium of the discounted repeated game in public
strategies. -/
def IsDiscountedPublicNash (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (σ : M.MonitoredProfile) : Prop :=
  M.IsεDiscountedPublicNash δ 0 σ

/-- Approximate perfect-public equilibrium: the profile is an approximate
discounted public Nash equilibrium at the root and after every nonempty public
history.  Separating the root avoids dependent casts around the unique
length-zero history. -/
def IsεPerfectPublicEquilibrium (M : G.PublicMonitoring) [DecidableEq ι]
    (δ ε : ℝ) (σ : M.MonitoredProfile) : Prop :=
  M.IsεDiscountedPublicNash δ ε σ ∧
    ∀ t (h : M.SignalHistory (t + 1)),
      M.IsεDiscountedPublicNash δ ε (M.after σ h)

/-- Perfect-public equilibrium under normalized discounted payoffs. -/
def IsPerfectPublicEquilibrium (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (σ : M.MonitoredProfile) : Prop :=
  M.IsεPerfectPublicEquilibrium δ 0 σ

/-- No player gains by changing only the current action and returning to the
prescribed public strategy from the next period onward. -/
def HasNoProfitableOneShotDeviation
    (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (σ : M.MonitoredProfile) : Prop :=
  ∀ who (a : G.Strategy who),
    M.discountedAveragePayoff δ σ who ≥
      M.discountedAveragePayoff δ
        (Function.update σ who (M.oneShotDeviation σ who a)) who

/-- One-shot sequential rationality at the root and after every nonempty
public history. -/
def HasNoProfitableOneShotDeviationAfterEveryHistory
    (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (σ : M.MonitoredProfile) : Prop :=
  M.HasNoProfitableOneShotDeviation δ σ ∧
    ∀ t (h : M.SignalHistory (t + 1)),
      M.HasNoProfitableOneShotDeviation δ (M.after σ h)

/-- Discounted public Nash is monotone in the approximation allowance. -/
theorem IsεDiscountedPublicNash.mono
    {M : G.PublicMonitoring} [DecidableEq ι]
    {δ ε ε' : ℝ} {σ : M.MonitoredProfile}
    (h : M.IsεDiscountedPublicNash δ ε σ) (hε : ε ≤ ε') :
    M.IsεDiscountedPublicNash δ ε' σ := by
  intro who dev
  have := h who dev
  linarith

/-- Approximate PPE is monotone in the approximation allowance. -/
theorem IsεPerfectPublicEquilibrium.mono
    {M : G.PublicMonitoring} [DecidableEq ι]
    {δ ε ε' : ℝ} {σ : M.MonitoredProfile}
    (h : M.IsεPerfectPublicEquilibrium δ ε σ) (hε : ε ≤ ε') :
    M.IsεPerfectPublicEquilibrium δ ε' σ :=
  ⟨h.1.mono hε, fun t hist => (h.2 t hist).mono hε⟩

/-- PPE implies discounted public Nash at the initial history. -/
theorem IsPerfectPublicEquilibrium.isDiscountedPublicNash
    {M : G.PublicMonitoring} [DecidableEq ι]
    {δ : ℝ} {σ : M.MonitoredProfile}
    (h : M.IsPerfectPublicEquilibrium δ σ) :
    M.IsDiscountedPublicNash δ σ :=
  h.1

/-- Discounted public Nash rules out every one-shot deviation. -/
theorem IsDiscountedPublicNash.hasNoProfitableOneShotDeviation
    {M : G.PublicMonitoring} [DecidableEq ι]
    {δ : ℝ} {σ : M.MonitoredProfile}
    (h : M.IsDiscountedPublicNash δ σ) :
    M.HasNoProfitableOneShotDeviation δ σ := by
  intro who a
  simpa [IsDiscountedPublicNash, IsεDiscountedPublicNash] using
    h who (M.oneShotDeviation σ who a)

/-- Every PPE is sequentially rational against one-shot deviations.  The
converse is the one-shot-deviation principle and requires a separate
continuity-at-infinity proof. -/
theorem IsPerfectPublicEquilibrium.hasNoProfitableOneShotDeviationAfterEveryHistory
    {M : G.PublicMonitoring} [DecidableEq ι]
    {δ : ℝ} {σ : M.MonitoredProfile}
    (h : M.IsPerfectPublicEquilibrium δ σ) :
    M.HasNoProfitableOneShotDeviationAfterEveryHistory δ σ :=
  ⟨IsDiscountedPublicNash.hasNoProfitableOneShotDeviation h.1,
    fun t hist => IsDiscountedPublicNash.hasNoProfitableOneShotDeviation
      (h.2 t hist)⟩

/-- Stationary repetition of a stage Nash equilibrium is a discounted public
Nash equilibrium under every public monitoring structure. -/
theorem stationaryMonitoredProfile_isDiscountedPublicNash_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι] [Finite G.Outcome]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ : Profile G} (hN : G.IsNash σ) :
    M.IsDiscountedPublicNash δ (M.stationaryMonitoredProfile σ) := by
  intro who dev
  obtain ⟨C, hC⟩ := G.exists_eu_abs_bound_of_finite_outcome who
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC σ)
  have hpay :
      M.discountedAveragePayoff δ
          (Function.update (M.stationaryMonitoredProfile σ) who dev) who ≤
        M.discountedAveragePayoff δ (M.stationaryMonitoredProfile σ) who := by
    refine M.discountedAveragePayoff_le_of_forall_stageEU_le hδ0 hδ1 who
      (fun t => M.abs_stageEU_le_of_forall_eu_abs_le
        (Function.update (M.stationaryMonitoredProfile σ) who dev) t who hC0 hC)
      (fun t => M.abs_stageEU_le_of_forall_eu_abs_le
        (M.stationaryMonitoredProfile σ) t who hC0 hC) ?_
    intro t
    rw [M.stageEU_stationaryMonitoredProfile σ t who]
    refine M.stageEU_le_const_of_forall
      (Function.update (M.stationaryMonitoredProfile σ) who dev) t who
      (B := G.eu σ who) (C := C) ?_ ?_ (hC σ)
    · intro hist
      have hprofile :
          (fun i => (Function.update (M.stationaryMonitoredProfile σ) who dev)
            i t hist) = Function.update σ who (dev t hist) := by
        funext i
        by_cases hi : i = who
        · subst hi
          simp
        · simp [Function.update, stationaryMonitoredProfile, hi]
      rw [hprofile]
      exact hN who _
    · intro hist
      exact hC _
  simpa only [add_zero] using hpay

/-- Stationary repetition of a stage Nash equilibrium is a PPE under every
public monitoring structure. -/
theorem stationaryMonitoredProfile_isPerfectPublicEquilibrium_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι] [Finite G.Outcome]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ : Profile G} (hN : G.IsNash σ) :
    M.IsPerfectPublicEquilibrium δ (M.stationaryMonitoredProfile σ) := by
  refine ⟨M.stationaryMonitoredProfile_isDiscountedPublicNash_of_isNash
    hδ0 hδ1 hN, ?_⟩
  intro t hist
  rw [M.after_stationaryMonitoredProfile σ hist]
  exact M.stationaryMonitoredProfile_isDiscountedPublicNash_of_isNash
    hδ0 hδ1 hN

/-! ### Compatibility with deterministic profile monitoring -/

@[simp] theorem discountedAveragePayoff_profileMonitoring
    (G : KernelGame ι) (δ : ℝ) (σ : G.RepeatedProfile) (who : ι) :
    G.profileMonitoring.discountedAveragePayoff δ σ who =
      G.discountedAveragePayoff δ σ who := by
  simp [discountedAveragePayoff, KernelGame.discountedAveragePayoff]

theorem isDiscountedPublicNash_profileMonitoring
    (G : KernelGame ι) [DecidableEq ι] (δ : ℝ) (σ : G.RepeatedProfile) :
    G.profileMonitoring.IsDiscountedPublicNash δ σ ↔
      G.IsDiscountedRepeatedNash δ σ := by
  simp only [IsDiscountedPublicNash, IsεDiscountedPublicNash,
    KernelGame.IsDiscountedRepeatedNash, add_zero,
    discountedAveragePayoff_profileMonitoring]

end PublicMonitoring

end KernelGame

end GameTheory
