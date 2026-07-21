/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Repeated.MonitoringDecomposition

/-!
# Self-Generating Payoff Sets under Public Monitoring

This file constructs the public strategy selected by an APS self-generating
set.  Promised payoff vectors are strategy states; after each public signal,
the state moves to the continuation payoff selected by the decomposition.
-/

noncomputable section

namespace GameTheory

namespace KernelGame

namespace PublicMonitoring

variable {ι : Type} {G : KernelGame ι}

/-- Coordinatewise boundedness of a payoff set. -/
def IsBoundedPayoffSet (W : Set (Payoff ι)) : Prop :=
  ∀ who, ∃ C : ℝ, ∀ v ∈ W, |v who| ≤ C

/-- Payoff vectors delivered by perfect-public equilibria. -/
def perfectPublicEquilibriumPayoffs
    (M : G.PublicMonitoring) [DecidableEq ι] (δ : ℝ) : Set (Payoff ι) :=
  {v | ∃ σ : M.MonitoredProfile,
    M.IsPerfectPublicEquilibrium δ σ ∧
      ∀ who, M.discountedAveragePayoff δ σ who = v who}

/-- The continuation-payoff vector delivered after each possible next public
signal. -/
def continuationPayoffAssignment
    (M : G.PublicMonitoring) (δ : ℝ) (σ : M.MonitoredProfile) :
    M.ContinuationAssignment :=
  fun y who => M.discountedAveragePayoff δ (M.afterSignal σ y) who

/-- Continuation payoffs are bounded whenever stage expected payoffs are
uniformly bounded. -/
theorem isBoundedContinuationPayoffAssignment_of_bounded
    (M : G.PublicMonitoring) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (σ : M.MonitoredProfile)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C) :
    M.IsBoundedContinuationAssignment
      (M.continuationPayoffAssignment δ σ) := by
  intro who
  obtain ⟨C, hC⟩ := hstage who
  let C' := max C 0
  have hC' : ∀ a : Profile G, |G.eu a who| ≤ C' :=
    fun a => (hC a).trans (le_max_left C 0)
  refine ⟨C', ?_⟩
  intro y
  exact M.abs_discountedAveragePayoff_le_of_forall_eu_abs_le
    hδ0 hδ1 (le_max_right C 0) (M.afterSignal σ y) who hC'

/-- The PPE payoff set is coordinatewise bounded when stage expected payoffs
are uniformly bounded. -/
theorem isBoundedPayoffSet_perfectPublicEquilibriumPayoffs_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι] {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C) :
    IsBoundedPayoffSet (M.perfectPublicEquilibriumPayoffs δ) := by
  intro who
  obtain ⟨C, hC⟩ := hstage who
  let C' := max C 0
  have hC' : ∀ a : Profile G, |G.eu a who| ≤ C' :=
    fun a => (hC a).trans (le_max_left C 0)
  refine ⟨C', ?_⟩
  rintro v ⟨σ, _hσ, hv⟩
  rw [← hv who]
  exact M.abs_discountedAveragePayoff_le_of_forall_eu_abs_le
    hδ0 hδ1 (le_max_right C 0) σ who hC'

/-- Finite-outcome convenience form of boundedness of the PPE payoff set. -/
theorem isBoundedPayoffSet_perfectPublicEquilibriumPayoffs
    (M : G.PublicMonitoring) [DecidableEq ι] [Finite G.Outcome]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    IsBoundedPayoffSet (M.perfectPublicEquilibriumPayoffs δ) := by
  apply M.isBoundedPayoffSet_perfectPublicEquilibriumPayoffs_of_bounded
    hδ0 hδ1
  exact fun who => G.exists_eu_abs_bound_of_finite_outcome who

namespace SelfGenerating

variable {M : G.PublicMonitoring} [DecidableEq ι]
variable {δ : ℝ} {W : Set (Payoff ι)}

/-- Current action profile selected from a self-generating decomposition. -/
noncomputable def action
    (h : M.SelfGenerating δ W) (v : W) : Profile G :=
  (h v.1 v.2).choose

/-- Public continuation assignment selected from a self-generating
decomposition. -/
noncomputable def continuation
    (h : M.SelfGenerating δ W) (v : W) : M.ContinuationAssignment :=
  (h v.1 v.2).choose_spec.choose

theorem continuation_bounded
    (h : M.SelfGenerating δ W) (v : W) :
    M.IsBoundedContinuationAssignment (h.continuation v) :=
  (h v.1 v.2).choose_spec.choose_spec.1

theorem continuation_mem
    (h : M.SelfGenerating δ W) (v : W) (y : M.Signal) :
    h.continuation v y ∈ W :=
  (h v.1 v.2).choose_spec.choose_spec.2.1 y

theorem promiseKeeping
    (h : M.SelfGenerating δ W) (v : W) :
    M.IsPromiseKeeping δ v.1 (h.action v) (h.continuation v) :=
  (h v.1 v.2).choose_spec.choose_spec.2.2.1

theorem enforceable
    (h : M.SelfGenerating δ W) (v : W) :
    M.IsEnforceable δ (h.action v) (h.continuation v) :=
  (h v.1 v.2).choose_spec.choose_spec.2.2.2

/-- Promise state reached after one public signal. -/
noncomputable def nextState
    (h : M.SelfGenerating δ W) (v : W) (y : M.Signal) : W :=
  ⟨h.continuation v y, h.continuation_mem v y⟩

@[simp] theorem nextState_val
    (h : M.SelfGenerating δ W) (v : W) (y : M.Signal) :
    (h.nextState v y).1 = h.continuation v y :=
  rfl

/-- Promise state reached after a finite chronological list of public
signals. -/
noncomputable def stateAfterSignals
    (h : M.SelfGenerating δ W) : W → List M.Signal → W
  | v, [] => v
  | v, y :: ys => h.stateAfterSignals (h.nextState v y) ys

@[simp] theorem stateAfterSignals_nil
    (h : M.SelfGenerating δ W) (v : W) :
    h.stateAfterSignals v [] = v :=
  rfl

@[simp] theorem stateAfterSignals_cons
    (h : M.SelfGenerating δ W) (v : W)
    (y : M.Signal) (ys : List M.Signal) :
    h.stateAfterSignals v (y :: ys) =
      h.stateAfterSignals (h.nextState v y) ys :=
  rfl

/-- Public strategy generated by repeatedly selecting the decomposition of
the current promised payoff state. -/
noncomputable def generatedProfile
    (h : M.SelfGenerating δ W) (v : W) : M.MonitoredProfile :=
  fun i _ hist => h.action (h.stateAfterSignals v (List.ofFn hist)) i

@[simp] theorem generatedProfile_zero
    (h : M.SelfGenerating δ W) (v : W) (i : ι)
    (hist : M.SignalHistory 0) :
    h.generatedProfile v i 0 hist = h.action v i := by
  simp [generatedProfile]

/-- The generated strategy continues from the selected next promise state. -/
theorem afterSignal_generatedProfile
    (h : M.SelfGenerating δ W) (v : W) (y : M.Signal) :
    M.afterSignal (h.generatedProfile v) y =
      h.generatedProfile (h.nextState v y) := by
  funext i n hist
  simp [afterSignal, generatedProfile, List.ofFn_succ]

/-- Iterated continuation follows the corresponding iterated promise-state
transition. -/
theorem afterSignals_generatedProfile
    (h : M.SelfGenerating δ W) (v : W) (ys : List M.Signal) :
    M.afterSignals (h.generatedProfile v) ys =
      h.generatedProfile (h.stateAfterSignals v ys) := by
  induction ys generalizing v with
  | nil => rfl
  | cons y ys ih =>
      rw [M.afterSignals_cons, h.afterSignal_generatedProfile, ih]
      rfl

/-- Continuation after an arbitrary public history is the generated strategy
from the promise state reached along that history. -/
theorem after_generatedProfile
    (h : M.SelfGenerating δ W) (v : W)
    {t : ℕ} (hist : M.SignalHistory t) :
    M.after (h.generatedProfile v) hist =
      h.generatedProfile (h.stateAfterSignals v (List.ofFn hist)) := by
  exact h.afterSignals_generatedProfile v (List.ofFn hist)

/-- The generated strategy realizes its current promised payoff.  The proof
uses Bellman contraction: after `N` recursive substitutions, the discrepancy
is at most `δ ^ N * (Cstage + Cpromise)`. -/
theorem generatedProfile_realizesPromise_of_bounds
    (h : M.SelfGenerating δ W)
    {who : ι} {Cstage Cpromise : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ a : Profile G, |G.eu a who| ≤ Cstage)
    (hpromise : ∀ q ∈ W, |q who| ≤ Cpromise)
    (v : W) :
    M.discountedAveragePayoff δ (h.generatedProfile v) who = v.1 who := by
  have hCstage0 : 0 ≤ Cstage :=
    le_trans (abs_nonneg _) (hstage (h.action v))
  have hCpromise0 : 0 ≤ Cpromise :=
    le_trans (abs_nonneg _) (hpromise v.1 v.2)
  have herror : ∀ N (q : W),
      |M.discountedAveragePayoff δ (h.generatedProfile q) who - q.1 who| ≤
        δ ^ N * (Cstage + Cpromise) := by
    intro N
    induction N with
    | zero =>
        intro q
        rw [pow_zero, one_mul]
        calc
          |M.discountedAveragePayoff δ (h.generatedProfile q) who - q.1 who| ≤
              |M.discountedAveragePayoff δ (h.generatedProfile q) who| +
                |q.1 who| := abs_sub _ _
          _ ≤ Cstage + Cpromise := by
            exact add_le_add
              (M.abs_discountedAveragePayoff_le_of_forall_eu_abs_le
                hδ0 hδ1 hCstage0 (h.generatedProfile q) who hstage)
              (hpromise q.1 q.2)
    | succ N ih =>
        intro q
        let B : ℝ := δ ^ N * (Cstage + Cpromise)
        let V : W → ℝ := fun r =>
          M.discountedAveragePayoff δ (h.generatedProfile r) who
        let Q : W → ℝ := fun r => r.1 who
        let p : PMF M.Signal := M.signalKernel (h.action q)
        have hVbound (y : M.Signal) : |V (h.nextState q y)| ≤
            Cstage + Cpromise := by
          exact (M.abs_discountedAveragePayoff_le_of_forall_eu_abs_le
            hδ0 hδ1 hCstage0 (h.generatedProfile (h.nextState q y))
            who hstage).trans (le_add_of_nonneg_right hCpromise0)
        have hQbound (y : M.Signal) : |Q (h.nextState q y)| ≤
            Cstage + Cpromise := by
          exact (hpromise _ (h.nextState q y).2).trans
            (le_add_of_nonneg_left hCstage0)
        have hpointUpper (y : M.Signal) :
            V (h.nextState q y) ≤ Q (h.nextState q y) + B := by
          have := abs_le.mp (ih (h.nextState q y))
          dsimp only [V, Q, B]
          linarith
        have hpointLower (y : M.Signal) :
            Q (h.nextState q y) ≤ V (h.nextState q y) + B := by
          have := abs_le.mp (ih (h.nextState q y))
          dsimp only [V, Q, B]
          linarith
        have hexpectUpper :
            Math.Probability.expect p (fun y => V (h.nextState q y)) ≤
              Math.Probability.expect p (fun y => Q (h.nextState q y)) + B :=
          Math.ProbabilityMassFunction.expect_le_expect_add_const_of_pointwise_bounded
            p _ _ B hVbound hQbound hpointUpper
        have hexpectLower :
            Math.Probability.expect p (fun y => Q (h.nextState q y)) ≤
              Math.Probability.expect p (fun y => V (h.nextState q y)) + B :=
          Math.ProbabilityMassFunction.expect_le_expect_add_const_of_pointwise_bounded
            p _ _ B hQbound hVbound hpointLower
        have hbell := M.discountedAveragePayoff_eq_head_add_expected
          hδ0 hδ1 hCstage0 (h.generatedProfile q) who hstage
        simp only [generatedProfile_zero,
          h.afterSignal_generatedProfile] at hbell
        have hbellV : V q = (1 - δ) * G.eu (h.action q) who +
            δ * Math.Probability.expect p
              (fun y => V (h.nextState q y)) := by
          simpa only [V, p] using hbell
        have hkeep :
            (1 - δ) * G.eu (h.action q) who +
                δ * Math.Probability.expect p
                  (fun y => Q (h.nextState q y)) = Q q := by
          have hcoord := congrFun (h.promiseKeeping q) who
          simpa only [IsPromiseKeeping, decomposedPayoff,
            p, Q, nextState_val] using hcoord
        have hupper : V q ≤ Q q + δ * B := by
          calc
            V q = (1 - δ) * G.eu (h.action q) who +
                δ * Math.Probability.expect p
                  (fun y => V (h.nextState q y)) := by
              simpa only [V, p] using hbell
            _ ≤ (1 - δ) * G.eu (h.action q) who +
                δ * (Math.Probability.expect p
                  (fun y => Q (h.nextState q y)) + B) := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_left hexpectUpper hδ0) _
            _ = Q q + δ * B := by rw [← hkeep]; ring
        have hlower : Q q ≤ V q + δ * B := by
          calc
            Q q = (1 - δ) * G.eu (h.action q) who +
                δ * Math.Probability.expect p
                  (fun y => Q (h.nextState q y)) := hkeep.symm
            _ ≤ (1 - δ) * G.eu (h.action q) who +
                δ * (Math.Probability.expect p
                  (fun y => V (h.nextState q y)) + B) := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_left hexpectLower hδ0) _
            _ = ((1 - δ) * G.eu (h.action q) who +
                δ * Math.Probability.expect p
                  (fun y => V (h.nextState q y))) + δ * B := by ring
            _ = V q + δ * B := by rw [← hbellV]
        have hB : δ * B = δ ^ (N + 1) * (Cstage + Cpromise) := by
          simp only [B, pow_succ]
          ring
        rw [← hB]
        apply abs_le.mpr
        constructor <;> dsimp only [V, Q] at hupper hlower ⊢ <;> linarith
  have hlimit : Filter.Tendsto
      (fun N => δ ^ N * (Cstage + Cpromise)) Filter.atTop (nhds 0) :=
    by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1).mul_const
          (Cstage + Cpromise)
  have hzero :
      |M.discountedAveragePayoff δ (h.generatedProfile v) who - v.1 who| ≤ 0 :=
    ge_of_tendsto' hlimit (fun N => herror N v)
  have heq :
      M.discountedAveragePayoff δ (h.generatedProfile v) who - v.1 who = 0 :=
    abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  exact sub_eq_zero.mp heq

/-- Coordinatewise-bounded payoff sets and bounded stage payoffs suffice for
every promise state to be realized by its generated strategy. -/
theorem generatedProfile_realizesPromise
    (h : M.SelfGenerating δ W)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C)
    (hW : IsBoundedPayoffSet W) (v : W) (who : ι) :
    M.discountedAveragePayoff δ (h.generatedProfile v) who = v.1 who := by
  obtain ⟨Cstage, hCstage⟩ := hstage who
  obtain ⟨Cpromise, hCpromise⟩ := hW who
  exact h.generatedProfile_realizesPromise_of_bounds
    hδ0 hδ1 hCstage hCpromise v

/-- The actual payoff from a one-shot deviation in the generated strategy is
the APS decomposed deviation payoff selected at the current promise state. -/
theorem discountedAveragePayoff_oneShotDeviation_eq_decomposedDeviationPayoff
    (h : M.SelfGenerating δ W)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C)
    (hW : IsBoundedPayoffSet W) (v : W)
    (who : ι) (dev : G.Strategy who) :
    M.discountedAveragePayoff δ
        (Function.update (h.generatedProfile v) who
          (M.oneShotDeviation (h.generatedProfile v) who dev)) who =
      M.decomposedDeviationPayoff δ (h.action v) (h.continuation v)
        who dev := by
  obtain ⟨C, hC⟩ := hstage who
  have hC0 : 0 ≤ C :=
    le_trans (abs_nonneg _) (hC (h.action v))
  let τ : M.MonitoredProfile :=
    Function.update (h.generatedProfile v) who
      (M.oneShotDeviation (h.generatedProfile v) who dev)
  have hroot :
      (fun i => τ i 0 (fun k => k.elim0)) =
        Function.update (h.action v) who dev := by
    funext i
    by_cases hi : i = who
    · subst hi
      simp [τ]
    · simp [τ, hi]
  have hbell := M.discountedAveragePayoff_eq_head_add_expected
    hδ0 hδ1 hC0 τ who hC
  have hcont (y : M.Signal) :
      M.afterSignal τ y = h.generatedProfile (h.nextState v y) := by
    dsimp only [τ]
    rw [M.afterSignal_update_oneShotDeviation,
      h.afterSignal_generatedProfile]
  rw [hroot] at hbell
  simp_rw [hcont] at hbell
  simp_rw [h.generatedProfile_realizesPromise hδ0 hδ1 hstage hW] at hbell
  simpa only [τ, decomposedDeviationPayoff, nextState_val] using hbell

/-- The generated strategy has no profitable one-shot deviation at its
current promise state. -/
theorem generatedProfile_hasNoProfitableOneShotDeviation
    (h : M.SelfGenerating δ W)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C)
    (hW : IsBoundedPayoffSet W) (v : W) :
    M.HasNoProfitableOneShotDeviation δ (h.generatedProfile v) := by
  intro who dev
  calc
    M.discountedAveragePayoff δ
        (Function.update (h.generatedProfile v) who
          (M.oneShotDeviation (h.generatedProfile v) who dev)) who =
        M.decomposedDeviationPayoff δ (h.action v) (h.continuation v)
          who dev :=
      h.discountedAveragePayoff_oneShotDeviation_eq_decomposedDeviationPayoff
        hδ0 hδ1 hstage hW v who dev
    _ ≤ M.decomposedPayoff δ (h.action v) (h.continuation v) who :=
      h.enforceable v who dev
    _ = v.1 who := congrFun (h.promiseKeeping v) who
    _ = M.discountedAveragePayoff δ (h.generatedProfile v) who :=
      (h.generatedProfile_realizesPromise hδ0 hδ1 hstage hW v who).symm

/-- One-shot optimality of the generated strategy holds after every public
history, including zero-probability histories. -/
theorem generatedProfile_hasNoProfitableOneShotDeviationAfterEveryHistory
    (h : M.SelfGenerating δ W)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C)
    (hW : IsBoundedPayoffSet W) (v : W) :
    M.HasNoProfitableOneShotDeviationAfterEveryHistory δ
      (h.generatedProfile v) := by
  constructor
  · exact h.generatedProfile_hasNoProfitableOneShotDeviation
      hδ0 hδ1 hstage hW v
  · intro t hist
    rw [h.after_generatedProfile]
    exact h.generatedProfile_hasNoProfitableOneShotDeviation
      hδ0 hδ1 hstage hW _

/-- The public strategy generated from a bounded self-generating set is a
perfect-public equilibrium. -/
theorem generatedProfile_isPerfectPublicEquilibrium
    (h : M.SelfGenerating δ W)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C)
    (hW : IsBoundedPayoffSet W) (v : W) :
    M.IsPerfectPublicEquilibrium δ (h.generatedProfile v) := by
  exact (h.generatedProfile_hasNoProfitableOneShotDeviationAfterEveryHistory
    hδ0 hδ1 hstage hW v).isPerfectPublicEquilibrium_of_bounded
      hδ0 hδ1 hstage

/-- Finite-outcome convenience form of the generated-strategy PPE theorem. -/
theorem generatedProfile_isPerfectPublicEquilibrium_of_finite_outcome
    [Finite G.Outcome]
    (h : M.SelfGenerating δ W)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hW : IsBoundedPayoffSet W) (v : W) :
    M.IsPerfectPublicEquilibrium δ (h.generatedProfile v) := by
  apply h.generatedProfile_isPerfectPublicEquilibrium hδ0 hδ1 _ hW
  exact fun who => G.exists_eu_abs_bound_of_finite_outcome who

/-- **APS self-generation theorem.** Every payoff in a coordinatewise-bounded
self-generating set is delivered by a perfect-public equilibrium. -/
theorem selfGenerating_subset_perfectPublicEquilibriumPayoffs
    (M : G.PublicMonitoring)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C)
    {W : Set (Payoff ι)} (hW : IsBoundedPayoffSet W)
    (h : M.SelfGenerating δ W) :
    W ⊆ M.perfectPublicEquilibriumPayoffs δ := by
  intro v hv
  let q : W := ⟨v, hv⟩
  exact ⟨h.generatedProfile q,
    h.generatedProfile_isPerfectPublicEquilibrium hδ0 hδ1 hstage hW q,
    fun who => h.generatedProfile_realizesPromise
      hδ0 hδ1 hstage hW q who⟩

/-- Finite-outcome convenience form of the APS self-generation theorem. -/
theorem selfGenerating_subset_perfectPublicEquilibriumPayoffs_of_finite_outcome
    (M : G.PublicMonitoring) [Finite G.Outcome]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {W : Set (Payoff ι)} (hW : IsBoundedPayoffSet W)
    (h : M.SelfGenerating δ W) :
    W ⊆ M.perfectPublicEquilibriumPayoffs δ := by
  apply selfGenerating_subset_perfectPublicEquilibriumPayoffs
    M hδ0 hδ1 _ hW h
  exact fun who => G.exists_eu_abs_bound_of_finite_outcome who

end SelfGenerating

/-- **APS decomposition of PPE payoffs.** Under bounded stage payoffs, the PPE
payoff set decomposes relative to itself. -/
theorem perfectPublicEquilibriumPayoffs_selfGenerating_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C) :
    M.SelfGenerating δ (M.perfectPublicEquilibriumPayoffs δ) := by
  intro v hv
  obtain ⟨σ, hσ, hv⟩ := hv
  let a : Profile G := fun i => σ i 0 (fun k => k.elim0)
  let w : M.ContinuationAssignment :=
    M.continuationPayoffAssignment δ σ
  refine ⟨a, w,
    M.isBoundedContinuationPayoffAssignment_of_bounded
      hδ0 hδ1 σ hstage, ?_, ?_, ?_⟩
  · intro y
    exact ⟨M.afterSignal σ y, hσ.afterSignal y, fun _ => rfl⟩
  · funext who
    obtain ⟨C, hC⟩ := hstage who
    let C' := max C 0
    have hC' : ∀ ρ : Profile G, |G.eu ρ who| ≤ C' :=
      fun ρ => (hC ρ).trans (le_max_left C 0)
    have hbell := M.discountedAveragePayoff_eq_head_add_expected
      hδ0 hδ1 (le_max_right C 0) σ who hC'
    change M.decomposedPayoff δ a w who = v who
    rw [← hv who]
    simpa only [decomposedPayoff, a, w, continuationPayoffAssignment] using
      hbell.symm
  · intro who dev
    obtain ⟨C, hC⟩ := hstage who
    let C' := max C 0
    have hC' : ∀ ρ : Profile G, |G.eu ρ who| ≤ C' :=
      fun ρ => (hC ρ).trans (le_max_left C 0)
    let τ : M.MonitoredProfile :=
      Function.update σ who (M.oneShotDeviation σ who dev)
    have hroot :
        (fun i => τ i 0 (fun k => k.elim0)) =
          Function.update a who dev := by
      funext i
      by_cases hi : i = who
      · subst hi
        simp [τ, a]
      · simp [τ, a, hi]
    have hcont (y : M.Signal) :
        M.afterSignal τ y = M.afterSignal σ y := by
      simp [τ]
    have hτbell := M.discountedAveragePayoff_eq_head_add_expected
      hδ0 hδ1 (le_max_right C 0) τ who hC'
    rw [hroot] at hτbell
    simp_rw [hcont] at hτbell
    have hσbell := M.discountedAveragePayoff_eq_head_add_expected
      hδ0 hδ1 (le_max_right C 0) σ who hC'
    calc
      M.decomposedDeviationPayoff δ a w who dev =
          M.discountedAveragePayoff δ τ who := by
        simpa only [decomposedDeviationPayoff, a, w,
          continuationPayoffAssignment] using hτbell.symm
      _ ≤ M.discountedAveragePayoff δ σ who :=
        hσ.isDiscountedPublicNash.hasNoProfitableOneShotDeviation who dev
      _ = M.decomposedPayoff δ a w who := by
        simpa only [decomposedPayoff, a, w,
          continuationPayoffAssignment] using hσbell

/-- Finite-outcome convenience form of APS decomposition of the PPE payoff
set. -/
theorem perfectPublicEquilibriumPayoffs_selfGenerating
    (M : G.PublicMonitoring) [DecidableEq ι] [Finite G.Outcome]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    M.SelfGenerating δ (M.perfectPublicEquilibriumPayoffs δ) := by
  apply M.perfectPublicEquilibriumPayoffs_selfGenerating_of_bounded hδ0 hδ1
  exact fun who => G.exists_eu_abs_bound_of_finite_outcome who

/-- The PPE payoff set is the greatest coordinatewise-bounded self-generating
set: it is self-generating, and every other such set consists of PPE payoffs. -/
theorem perfectPublicEquilibriumPayoffs_greatest_bounded_selfGenerating
    (M : G.PublicMonitoring) [DecidableEq ι]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hstage : ∀ who : ι, ∃ C : ℝ,
      ∀ a : Profile G, |G.eu a who| ≤ C) :
    M.SelfGenerating δ (M.perfectPublicEquilibriumPayoffs δ) ∧
      ∀ W : Set (Payoff ι), IsBoundedPayoffSet W →
        M.SelfGenerating δ W →
          W ⊆ M.perfectPublicEquilibriumPayoffs δ := by
  refine ⟨M.perfectPublicEquilibriumPayoffs_selfGenerating_of_bounded
    hδ0 hδ1 hstage, ?_⟩
  intro W hW hself
  exact SelfGenerating.selfGenerating_subset_perfectPublicEquilibriumPayoffs
    M hδ0 hδ1 hstage hW hself

end PublicMonitoring

end KernelGame

end GameTheory
