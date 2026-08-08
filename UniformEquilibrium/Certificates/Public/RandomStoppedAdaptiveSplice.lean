/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.BoundedStoppingFactorization
import UniformEquilibrium.Certificates.Public.FiniteChildAdaptivePotentialFamily

/-!
# Adaptive suffixes after a bounded public stopping time

This file develops the expectation-level identities needed to splice child
adaptive systems after a bounded causal public stopping time.  The actual
root law is related to the dependent stopped-base/suffix law through the
explicit joint-law factorization interface.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι Child : Type} {G : StochasticGame ι}

namespace FiniteChildAdaptivePotentialFamily

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {error : ℝ}

/-- Child profiles indexed by stopped public bases through an observation
map. -/
def observedStoppedProfile
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ}
    (observe : G.BoundedStoppedHistory fuel → Child) :
    G.BoundedStoppedHistory fuel → G.BehaviorProfile :=
  fun base => family.profile (observe base)

/-- Lower child potential indexed by a stopped public base. -/
def stoppedLowerPotential
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ}
    (observe : G.BoundedStoppedHistory fuel → Child) (who : ι) :
    G.BoundedStoppedHistory fuel → G.HistoryPotential :=
  fun base => (family.system (observe base)).lowerPotential who

/-- Upper child potential indexed by a stopped public base. -/
def stoppedUpperPotential
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ}
    (observe : G.BoundedStoppedHistory fuel → Child) (who : ι) :
    G.BoundedStoppedHistory fuel → G.HistoryPotential :=
  fun base => (family.system (observe base)).upperPotential who

/-- Deviation child potential indexed by a stopped public base. -/
def stoppedDeviationPotential
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ}
    (observe : G.BoundedStoppedHistory fuel → Child) (who : ι) :
    G.BoundedStoppedHistory fuel → G.HistoryPotential :=
  fun base => (family.system (observe base)).deviationPotential who

/-- The three scalar child charges in the stopped-base indexing used by
`CommonRootChildChargeTailBound`. -/
def stoppedLowerCharge
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ}
    (observe : G.BoundedStoppedHistory fuel → Child) :
    G.BoundedStoppedHistory fuel → ι → ℕ → ℝ :=
  fun base => (family.system (observe base)).lowerCharge

def stoppedUpperCharge
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ}
    (observe : G.BoundedStoppedHistory fuel → Child) :
    G.BoundedStoppedHistory fuel → ι → ℕ → ℝ :=
  fun base => (family.system (observe base)).upperCharge

def stoppedDeviationCharge
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ}
    (observe : G.BoundedStoppedHistory fuel → Child) :
    ∀ _base : G.BoundedStoppedHistory fuel,
      ∀ who, G.BehaviorStrategy who → ℕ → ℝ :=
  fun base => (family.system (observe base)).deviationCharge

end FiniteChildAdaptivePotentialFamily

/-- Reconstructing a stopped suffix does not change the current-stage payoff
relative to ordinary history rebasing. -/
theorem stageEUAt_rootHistoryOfStoppedSuffix
    [Fintype ι] {fuel total : ℕ}
    (profile : G.BehaviorProfile)
    (hfuel : fuel ≤ total)
    (path : G.RootHorizonStoppedSuffix fuel total)
    (who : ι) :
    G.stageEUAt profile
        (G.rootHistoryOfStoppedSuffix hfuel path) who =
      G.stageEUAt
        (G.afterHistoryProfile profile path.1.2) path.2 who := by
  let hlength := G.stoppedLength_le_rootHorizon hfuel path.1
  let hadd :
      path.1.1.val + (total - path.1.1.val) = total :=
    Nat.add_sub_of_le hlength
  change
    G.stageEUAt profile
        (cast (congrArg G.Hist hadd)
          (G.appendHist path.1.2 path.2)) who =
      G.stageEUAt profile
        (G.appendHist path.1.2 path.2) who
  have hpackaged :
      (⟨total,
        cast (congrArg G.Hist hadd)
          (G.appendHist path.1.2 path.2)⟩ :
          Σ time, G.Hist time) =
        ⟨path.1.1.val + (total - path.1.1.val),
          G.appendHist path.1.2 path.2⟩ := by
    apply Sigma.ext hadd.symm
    exact cast_heq _ _
  exact congrArg
    (fun packaged : Σ time, G.Hist time =>
      G.stageEUAt profile packaged.2 who)
    hpackaged

/-- At a common root horizon, exact stopped-suffix disintegration turns the
root stage payoff into the stopped-law average of conditional suffix stage
payoffs. -/
theorem expectedStagePayoff_eq_stoppedSuffix
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ} (profile : G.BehaviorProfile)
    (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total)
    (hsplice :
      G.IsRootStoppedSuffixDisintegration
        profile initial selector hfuel)
    (who : ι) :
    G.expectedStagePayoff profile initial total who =
      expect (G.stoppedHistoryLaw profile initial selector) fun base =>
        G.expectedStagePayoff
          (G.afterHistoryProfile profile base.2) base.2.2
          (total - base.1.val) who := by
  unfold expectedStagePayoff
  rw [G.expect_rootHistory_eq_stoppedSuffix
    profile initial selector hfuel hsplice]
  unfold rootHorizonStoppedSuffixLaw
  rw [expect_bind]
  apply congrArg
    (expect (G.stoppedHistoryLaw profile initial selector))
  funext base
  rw [expect_map]
  exact congrArg
    (expect
      (G.histDist (G.afterHistoryProfile profile base.2)
        base.2.2 (total - base.1.val)))
    (funext fun suffix =>
      G.stageEUAt_rootHistoryOfStoppedSuffix
        profile hfuel ⟨base, suffix⟩ who)

/-- The support-local conditional-kernel identity supplies the exact joint
law interface used by stopped adaptive-splice calculations. -/
theorem causalDispatcherJointLawAt_of_conditionalKernelAdd
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hkernel :
      G.IsStoppedSuffixConditionalKernelAdd
        (suffixLength := suffixLength) profile initial selector) :
    G.CausalDispatcherJointLawAt profile initial selector
      (Nat.le_add_right fuel suffixLength) := by
  rw [G.causalDispatcherJointLawAt_iff_factorization]
  exact G.rootStoppedPath_factorization_add_of_conditionalKernel
    profile initial selector hkernel

/-- Before the fuel horizon use one scalar prefix value; afterwards evaluate
the selected child potential on the dependent stopped suffix. -/
def rootStoppedChildHistoryPotential {fuel : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (prefixValue : ℝ)
    (childPotential :
      G.BoundedStoppedHistory fuel → G.HistoryPotential) :
    G.HistoryPotential :=
  fun time history =>
    if htime : fuel ≤ time then
      let path :=
        G.rootStoppedPathOfHistory selector htime history
      childPotential path.1 (time - path.1.1.val) path.2
    else
      prefixValue

/-- Joint-law factorization identifies the root expectation of the stopped
child potential with the stopped-law average of conditional child
expectations. -/
theorem expectedHistoryValue_rootStoppedChild_eq
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (prefixValue : ℝ)
    (childPotential :
      G.BoundedStoppedHistory fuel → G.HistoryPotential)
    (hfuel : fuel ≤ total)
    (joint :
      G.CausalDispatcherJointLawAt
        profile initial selector hfuel) :
    G.expectedHistoryValue profile initial
        (G.rootStoppedChildHistoryPotential
          selector prefixValue childPotential) total =
      expect (G.stoppedHistoryLaw profile initial selector) fun base =>
        G.expectedHistoryValue
          (G.afterHistoryProfile profile base.2) base.2.2
          (childPotential base) (total - base.1.val) := by
  unfold expectedHistoryValue rootStoppedChildHistoryPotential
  simp only [dif_pos hfuel]
  let pathValue : G.RootHorizonStoppedSuffix fuel total → ℝ :=
    fun path =>
      childPotential path.1 (total - path.1.1.val) path.2
  calc
    expect (G.histDist profile initial total)
        (fun history =>
          childPotential
            (G.rootStoppedPathOfHistory selector hfuel history).1
            (total -
              (G.rootStoppedPathOfHistory
                selector hfuel history).1.1.val)
            (G.rootStoppedPathOfHistory selector hfuel history).2) =
      expect
        ((G.histDist profile initial total).map
          (G.rootStoppedPathOfHistory selector hfuel))
        pathValue := by
          rw [expect_map]
    _ =
      expect
        (G.rootHorizonStoppedSuffixLaw
          profile initial selector total) pathValue := by
          rw [joint.factorization]
    _ =
      expect (G.stoppedHistoryLaw profile initial selector) fun base =>
        G.expectedHistoryValue
          (G.afterHistoryProfile profile base.2) base.2.2
          (childPotential base) (total - base.1.val) := by
          unfold rootHorizonStoppedSuffixLaw
          rw [expect_bind]
          apply congrArg
            (expect (G.stoppedHistoryLaw profile initial selector))
          funext base
          rw [expect_map]
          rfl

/-- Exact stopped-target invariance needed at the deviation boundary.

The prefix deviation potential is fixed before a deviation is chosen.  This
condition says that every unilateral deviation gives its selected child
initial deviation potential the same stopped-law expectation. -/
def IsDeviationStoppedTargetInvariant
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (deviationTarget :
      G.BoundedStoppedHistory fuel → ι → ℝ) : Prop :=
  ∀ who (deviation : G.BehaviorStrategy who),
    expect
        (G.stoppedHistoryLaw
          (Function.update profile who deviation) initial selector)
        (fun base => deviationTarget base who) =
      expect (G.stoppedHistoryLaw profile initial selector)
        (fun base => deviationTarget base who)

/-- The exact common-root tail budget not implied by an ordinary child
Cesàro bound when scalar charges may be signed.

For each root time after `fuel`, the selected child is charged at its local
time `rootTime - stopTime`.  The three fields state precisely the normalized
tail estimates required by a parent adaptive system. -/
structure CommonRootChildChargeTailBound
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (lowerCharge upperCharge :
      G.BoundedStoppedHistory fuel → ι → ℕ → ℝ)
    (deviationCharge :
      ∀ (_base : G.BoundedStoppedHistory fuel) (who : ι),
        G.BehaviorStrategy who → ℕ → ℝ)
    (error : ℝ) where
  horizon : ℕ
  horizon_ge_two : 2 ≤ horizon
  lower : ∀ who total, horizon ≤ total →
    (total : ℝ)⁻¹ *
        ∑ rootTime ∈ Finset.Ico fuel total,
          expect (G.stoppedHistoryLaw profile initial selector)
            (fun base =>
              lowerCharge base who
                (rootTime - base.1.val)) ≤
      error
  upper : ∀ who total, horizon ≤ total →
    (total : ℝ)⁻¹ *
        ∑ rootTime ∈ Finset.Ico fuel total,
          expect (G.stoppedHistoryLaw profile initial selector)
            (fun base =>
              upperCharge base who
                (rootTime - base.1.val)) ≤
      error
  deviation :
    ∀ who (strategy : G.BehaviorStrategy who) total,
      horizon ≤ total →
        (total : ℝ)⁻¹ *
            ∑ rootTime ∈ Finset.Ico fuel total,
              expect
                (G.stoppedHistoryLaw
                  (Function.update profile who strategy)
                  initial selector)
                (fun base =>
                  deviationCharge base who
                    (G.afterHistoryStrategy strategy base.2)
                    (rootTime - base.1.val)) ≤
          error

/-- A uniform nonnegative child charge bound is one sufficient way to avoid
the signed-tail obstruction.  This structure records the exact condition
without strengthening the base adaptive-certificate interface. -/
structure NonnegativeChildScalarCharges
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (lowerCharge upperCharge :
      G.BoundedStoppedHistory fuel → ι → ℕ → ℝ)
    (deviationCharge :
      ∀ (_base : G.BoundedStoppedHistory fuel) (who : ι),
        G.BehaviorStrategy who → ℕ → ℝ) : Prop where
  lower : ∀ (base : G.BoundedStoppedHistory fuel)
    (who : ι) (time : ℕ), 0 ≤ lowerCharge base who time
  upper : ∀ (base : G.BoundedStoppedHistory fuel)
    (who : ι) (time : ℕ), 0 ≤ upperCharge base who time
  deviation :
    ∀ (base : G.BoundedStoppedHistory fuel) (who : ι)
      (strategy : G.BehaviorStrategy who) (time : ℕ),
      0 ≤ deviationCharge base who strategy time

/-- Removing an initial segment from a nonnegative scalar sequence cannot
increase its sum, even when the retained indices are shifted by a bounded
stopping time. -/
theorem sum_Ico_sub_le_sum_range_of_nonneg
    (charge : ℕ → ℝ) (stop fuel total : ℕ)
    (stop_le_fuel : stop ≤ fuel) (fuel_le_total : fuel ≤ total)
    (charge_nonneg : ∀ time, 0 ≤ charge time) :
    ∑ rootTime ∈ Finset.Ico fuel total,
        charge (rootTime - stop) ≤
      ∑ time ∈ Finset.range total, charge time := by
  rw [Finset.sum_Ico_eq_sum_range]
  calc
    ∑ rootTime ∈ Finset.range (total - fuel),
        charge (fuel + rootTime - stop) =
        ∑ rootTime ∈ Finset.range (total - fuel),
          charge ((fuel - stop) + rootTime) := by
            apply Finset.sum_congr rfl
            intro rootTime _
            congr 1
            omega
    _ =
        ∑ time ∈
            Finset.Ico (fuel - stop)
              ((fuel - stop) + (total - fuel)),
          charge time := by
            symm
            simpa only [Nat.add_sub_cancel_left] using
              Finset.sum_Ico_eq_sum_range
                charge (fuel - stop)
                  ((fuel - stop) + (total - fuel))
    _ ≤ ∑ time ∈ Finset.range total, charge time := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro time htime
        simp only [Finset.mem_Ico, Finset.mem_range] at htime ⊢
        omega
      · intro time _ _
        exact charge_nonneg time

/-- Average the shifted-tail estimate over a finite stopped-base law. -/
theorem normalized_expect_Ico_sub_le_of_nonneg
    {Base : Type} [Finite Base]
    (law : PMF Base) (stop : Base → ℕ)
    (charge : Base → ℕ → ℝ)
    (fuel total : ℕ) (error : ℝ)
    (stop_le_fuel : ∀ base, stop base ≤ fuel)
    (fuel_le_total : fuel ≤ total)
    (charge_nonneg : ∀ base time, 0 ≤ charge base time)
    (full_bound : ∀ base,
      (total : ℝ)⁻¹ *
          ∑ time ∈ Finset.range total, charge base time ≤
        error) :
    (total : ℝ)⁻¹ *
        ∑ rootTime ∈ Finset.Ico fuel total,
          expect law (fun base =>
            charge base (rootTime - stop base)) ≤
      error := by
  classical
  letI : Fintype Base := Fintype.ofFinite Base
  have sum_expect :
      ∑ rootTime ∈ Finset.Ico fuel total,
          expect law (fun base =>
            charge base (rootTime - stop base)) =
        expect law (fun base =>
          ∑ rootTime ∈ Finset.Ico fuel total,
            charge base (rootTime - stop base)) := by
    simp only [expect_eq_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro base _
    rw [Finset.mul_sum]
  rw [sum_expect, ← expect_const_mul]
  calc
    expect law (fun base =>
        (total : ℝ)⁻¹ *
          ∑ rootTime ∈ Finset.Ico fuel total,
            charge base (rootTime - stop base)) ≤
      expect law (fun _ => error) := by
        apply expect_mono
        intro base
        have tail_le :=
          sum_Ico_sub_le_sum_range_of_nonneg
            (charge base) (stop base) fuel total
            (stop_le_fuel base) fuel_le_total
            (charge_nonneg base)
        exact
          (mul_le_mul_of_nonneg_left tail_le (by positivity)).trans
            (full_bound base)
    _ = error := expect_const _ _

/-- Nonnegative child scalar charges turn ordinary child Cesàro bounds into
the common-root tail bounds required after a bounded random stopping time. -/
def FiniteChildAdaptivePotentialFamily.commonRootChildChargeTailBound_of_nonnegative
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)] [Fintype Child]
    {entry : Child → G.State} {target : Child → Payoff ι}
    {error : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (observe : G.BoundedStoppedHistory fuel → Child)
    (nonnegative :
      G.NonnegativeChildScalarCharges
        (family.stoppedLowerCharge observe)
        (family.stoppedUpperCharge observe)
        (family.stoppedDeviationCharge observe)) :
    G.CommonRootChildChargeTailBound
      profile initial selector
      (family.stoppedLowerCharge observe)
      (family.stoppedUpperCharge observe)
      (family.stoppedDeviationCharge observe) error where
  horizon := max fuel family.commonHorizon
  horizon_ge_two :=
    le_trans family.commonHorizon_ge_two
      (Nat.le_max_right fuel family.commonHorizon)
  lower := by
    intro who total htotal
    apply normalized_expect_Ico_sub_le_of_nonneg
    · intro base
      exact Nat.lt_succ_iff.mp base.1.isLt
    · exact
        le_trans (Nat.le_max_left fuel family.commonHorizon) htotal
    · intro base time
      exact nonnegative.lower base who time
    · intro base
      exact
        (family.system (observe base)).lower_charge_cesaro who total
          (le_trans
            (family.horizon_le_common (observe base))
            (le_trans
              (Nat.le_max_right fuel family.commonHorizon) htotal))
  upper := by
    intro who total htotal
    apply normalized_expect_Ico_sub_le_of_nonneg
    · intro base
      exact Nat.lt_succ_iff.mp base.1.isLt
    · exact
        le_trans (Nat.le_max_left fuel family.commonHorizon) htotal
    · intro base time
      exact nonnegative.upper base who time
    · intro base
      exact
        (family.system (observe base)).upper_charge_cesaro who total
          (le_trans
            (family.horizon_le_common (observe base))
            (le_trans
              (Nat.le_max_right fuel family.commonHorizon) htotal))
  deviation := by
    intro who strategy total htotal
    apply normalized_expect_Ico_sub_le_of_nonneg
    · intro base
      exact Nat.lt_succ_iff.mp base.1.isLt
    · exact
        le_trans (Nat.le_max_left fuel family.commonHorizon) htotal
    · intro base time
      exact
        nonnegative.deviation base who
          (G.afterHistoryStrategy strategy base.2) time
    · intro base
      exact
        (family.system (observe base)).deviation_charge_cesaro
          who (G.afterHistoryStrategy strategy base.2) total
          (le_trans
            (family.horizon_le_common (observe base))
            (le_trans
              (Nat.le_max_right fuel family.commonHorizon) htotal))

/-- Joint-law factorization is target- and charge-free: it can be reused
unchanged for any stopped target and any scalar charge family.  Consequently
the two interfaces above are logically additional data, rather than
consequences hidden inside factorization. -/
theorem CausalDispatcherJointLawAt.reuse_for_boundaryData
    [Fintype ι] {fuel total : ℕ}
    {profile : G.BehaviorProfile} {initial : G.State}
    {selector : G.BoundedPublicStopSelector fuel}
    {hfuel : fuel ≤ total}
    (joint :
      G.CausalDispatcherJointLawAt
        profile initial selector hfuel)
    (_deviationTarget :
      G.BoundedStoppedHistory fuel → ι → ℝ)
    (_lowerCharge _upperCharge :
      G.BoundedStoppedHistory fuel → ι → ℕ → ℝ) :
    G.CausalDispatcherJointLawAt
      profile initial selector hfuel :=
  joint

end StochasticGame
end GameTheory
