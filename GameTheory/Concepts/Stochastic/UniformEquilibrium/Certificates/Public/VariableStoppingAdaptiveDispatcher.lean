/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.FinitePublicCoinStoppedExpectation
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.CausalStoppingEventRatio
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.RandomStoppedSignedChargeTail

/-!
# Adaptive dispatch at a bounded public stopping time

This file composes the existing stopped-base/suffix factorization with child
adaptive systems.  The strategic profile enters the selected child
immediately, through `causalTerminalChildDispatcher`; the accounting
potentials are allowed a separately constructed prefix part before the common
fuel horizon.

The remaining strategic inputs are isolated explicitly.
`VariableStoppingPrefixLaw` states all pre-fuel adaptive inequalities and
charge budgets.  Constructing it from a particular
`FinitePublicCoinStoppingRegion`, online rule, profile, and potential family
is still an application obligation.  At and after the fuel horizon,
causality supplies the stopped-suffix joint law for the dispatcher and every
unilateral update; `variableStoppingSuffixCaps` derives the process
inequalities from child certificates, given a common-root child-charge tail
bound.  The final composition also requires the three initial whole-vector
target anchors.  A root unilateral deviation is conditioned at each
realized stopped base as `afterHistoryStrategy deviation base`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι Child : Type} {G : StochasticGame ι}

/-- Use a prefix potential before the common fuel horizon, and the potential
of the realized stopped child afterwards. -/
def prefixThenStoppedChildHistoryPotential {fuel : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (prefixPotential : G.HistoryPotential)
    (childPotential :
      G.BoundedStoppedHistory fuel → G.HistoryPotential) :
    G.HistoryPotential :=
  fun time history =>
    if htime : fuel ≤ time then
      let path := G.rootStoppedPathOfHistory selector htime history
      childPotential path.1 (time - path.1.1.val) path.2
    else
      prefixPotential time history

/-- Scalar charge of the realized stopped child, expressed at root time. -/
def stoppedChildScalarCharge
    [Fintype ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (childCharge :
      G.BoundedStoppedHistory fuel → ι → ℕ → ℝ)
    (who : ι) (rootTime : ℕ) : ℝ :=
  expect (G.stoppedHistoryLaw profile initial selector) fun base =>
    childCharge base who (rootTime - base.1.val)

/-- Deviation charge after conditioning the one root deviation at each
stopped public base. -/
def stoppedChildDeviationScalarCharge
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (childCharge :
      ∀ (_base : G.BoundedStoppedHistory fuel) (who : ι),
        G.BehaviorStrategy who → ℕ → ℝ)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (rootTime : ℕ) : ℝ :=
  expect
      (G.stoppedHistoryLaw
        (Function.update profile who deviation) initial selector)
      fun base =>
        childCharge base who
          (G.afterHistoryStrategy deviation base.2)
          (rootTime - base.1.val)

/-- Select a finite-prefix scalar charge before `fuel`, and the stopped child
charge afterwards. -/
def prefixThenScalarCharge {fuel : ℕ}
    (prefixCharge suffixCharge : ℕ → ℝ) : ℕ → ℝ :=
  fun time => if fuel ≤ time then suffixCharge time else prefixCharge time

/-- The abstract pre-fuel adaptive certificate.

The fields are exactly the adaptive inequalities that concern a time strictly
before the common fuel horizon.  `prefixCost` is a cumulative, not normalized,
bound; `amortized` records the horizon after which that fixed cost contributes
at most `error` to a Cesàro average.  The stored region and rank bound are
bookkeeping data; this structure does not assert that the region realizes the
supplied online selector, profile, or potentials.  A future compatibility
constructor must establish that link and prove all six prefix inequalities
and all three charge budgets. -/
structure VariableStoppingPrefixLaw
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State) (fuel : ℕ)
    (lowerPotential upperPotential deviationPotential :
      ι → G.HistoryPotential)
    (lowerCharge upperCharge : ι → ℕ → ℝ)
    (deviationCharge :
      ∀ who, G.BehaviorStrategy who → ℕ → ℝ)
    (error : ℝ) where
  region : G.FinitePublicCoinStoppingRegion
  rank_le_fuel : region.rank initial ≤ fuel
  horizon : ℕ
  prefixCost : ℝ
  horizon_ge_two : 2 ≤ horizon
  lower_submartingale : ∀ who time, time < fuel →
    G.expectedHistoryValue profile initial
        (lowerPotential who) time ≤
      G.expectedHistoryValue profile initial
        (lowerPotential who) (time + 1)
  lower_stage : ∀ who time, time < fuel →
    G.expectedHistoryValue profile initial
        (lowerPotential who) time ≤
      G.expectedStagePayoff profile initial time who +
        lowerCharge who time
  upper_supermartingale : ∀ who time, time < fuel →
    G.expectedHistoryValue profile initial
        (upperPotential who) (time + 1) ≤
      G.expectedHistoryValue profile initial
        (upperPotential who) time
  upper_stage : ∀ who time, time < fuel →
    G.expectedStagePayoff profile initial time who ≤
      G.expectedHistoryValue profile initial
          (upperPotential who) time +
        upperCharge who time
  deviation_supermartingale :
    ∀ who (deviation : G.BehaviorStrategy who) time, time < fuel →
      G.expectedHistoryValue
          (Function.update profile who deviation) initial
          (deviationPotential who) (time + 1) ≤
        G.expectedHistoryValue
          (Function.update profile who deviation) initial
          (deviationPotential who) time
  deviation_stage :
    ∀ who (deviation : G.BehaviorStrategy who) time, time < fuel →
      G.expectedStagePayoff
          (Function.update profile who deviation) initial time who ≤
        G.expectedHistoryValue
            (Function.update profile who deviation) initial
            (deviationPotential who) time +
          deviationCharge who deviation time
  lower_prefix_cost : ∀ who,
    ∑ time ∈ Finset.range fuel, lowerCharge who time ≤ prefixCost
  upper_prefix_cost : ∀ who,
    ∑ time ∈ Finset.range fuel, upperCharge who time ≤ prefixCost
  deviation_prefix_cost :
    ∀ who (deviation : G.BehaviorStrategy who),
      ∑ time ∈ Finset.range fuel,
          deviationCharge who deviation time ≤ prefixCost
  amortized : ∀ total, horizon ≤ total →
    (total : ℝ)⁻¹ * prefixCost ≤ error

/-- Above the common fuel horizon, the prefix branch of the combined
potential is irrelevant and the existing joint-law theorem applies. -/
theorem expectedHistoryValue_prefixThenStoppedChild_eq
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (prefixPotential : G.HistoryPotential)
    (childPotential :
      G.BoundedStoppedHistory fuel → G.HistoryPotential)
    (hfuel : fuel ≤ total)
    (joint :
      G.CausalDispatcherJointLawAt
        profile initial selector hfuel) :
    G.expectedHistoryValue profile initial
        (G.prefixThenStoppedChildHistoryPotential
          selector prefixPotential childPotential) total =
      expect (G.stoppedHistoryLaw profile initial selector) fun base =>
        G.expectedHistoryValue
          (G.afterHistoryProfile profile base.2) base.2.2
          (childPotential base) (total - base.1.val) := by
  have hpotential :
      G.expectedHistoryValue profile initial
          (G.prefixThenStoppedChildHistoryPotential
            selector prefixPotential childPotential) total =
        G.expectedHistoryValue profile initial
          (G.rootStoppedChildHistoryPotential
            selector 0 childPotential) total := by
    unfold expectedHistoryValue
    apply congrArg (expect (G.histDist profile initial total))
    funext history
    simp only [prefixThenStoppedChildHistoryPotential,
      rootStoppedChildHistoryPotential, dif_pos hfuel]
  rw [hpotential]
  exact G.expectedHistoryValue_rootStoppedChild_eq
    profile initial selector 0 childPotential hfuel joint

/-- Causality supplies the stopped-suffix joint law at an arbitrary root
horizon above the fuel, not only at a horizon syntactically written as an
addition. -/
theorem causalDispatcherJointLawAt_of_causal
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (causal : G.IsCausalBoundedStopSelector selector)
    (hfuel : fuel ≤ total) :
    G.CausalDispatcherJointLawAt
      profile initial selector hfuel := by
  obtain ⟨suffixLength, rfl⟩ :=
    Nat.exists_eq_add_of_le hfuel
  exact G.causalDispatcherJointLawAt_add_of_causal
    profile initial selector causal

private theorem jointToDisintegration
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (causal : G.IsCausalBoundedStopSelector selector)
    (hfuel : fuel ≤ total)
    (joint :
      G.CausalDispatcherJointLawAt
        profile initial selector hfuel) :
    G.IsRootStoppedSuffixDisintegration
      profile initial selector hfuel where
  causal := causal
  law_eq := by
    calc
      G.histDist profile initial total =
          ((G.histDist profile initial total).map
            (G.rootStoppedPathOfHistory selector hfuel)).map
            (G.rootHistoryOfStoppedSuffix hfuel) :=
        joint.reconstruct_actual.symm
      _ =
          (G.rootHorizonStoppedSuffixLaw
            profile initial selector total).map
            (G.rootHistoryOfStoppedSuffix hfuel) := by
        rw [joint.factorization]
      _ =
          G.reconstructedRootHistoryLaw
            profile initial selector hfuel := rfl

/-- Combine one explicitly bounded prefix with a normalized stopped-child
tail. -/
theorem normalized_prefixThenScalarCharge_le
    {fuel total : ℕ}
    (prefixCharge suffixCharge : ℕ → ℝ)
    (prefixCost prefixError suffixError : ℝ)
    (hfuel : fuel ≤ total)
    (hprefix :
      ∑ time ∈ Finset.range fuel, prefixCharge time ≤ prefixCost)
    (hamortized :
      (total : ℝ)⁻¹ * prefixCost ≤ prefixError)
    (htail :
      (total : ℝ)⁻¹ *
          ∑ time ∈ Finset.Ico fuel total, suffixCharge time ≤
        suffixError) :
    (total : ℝ)⁻¹ *
        ∑ time ∈ Finset.range total,
          prefixThenScalarCharge
            (fuel := fuel) prefixCharge suffixCharge time ≤
      prefixError + suffixError := by
  have hprefixPart :
      ∑ time ∈ Finset.range fuel,
          prefixThenScalarCharge
            (fuel := fuel) prefixCharge suffixCharge time =
        ∑ time ∈ Finset.range fuel, prefixCharge time := by
    apply Finset.sum_congr rfl
    intro time htime
    have hbefore : ¬fuel ≤ time := by
      exact Nat.not_le.mpr (Finset.mem_range.mp htime)
    simp only [prefixThenScalarCharge, hbefore, ↓reduceIte]
  have htailPart :
      ∑ time ∈ Finset.Ico fuel total,
          prefixThenScalarCharge
            (fuel := fuel) prefixCharge suffixCharge time =
        ∑ time ∈ Finset.Ico fuel total, suffixCharge time := by
    apply Finset.sum_congr rfl
    intro time htime
    simp only [prefixThenScalarCharge,
      (Finset.mem_Ico.mp htime).1, ↓reduceIte]
  rw [← Finset.sum_range_add_sum_Ico _ hfuel,
    hprefixPart, htailPart, mul_add]
  exact add_le_add
    ((mul_le_mul_of_nonneg_left hprefix (by positivity)).trans
      hamortized)
    htail

/-- Output of the stopped-suffix disintegration operation.

Concrete child families produce these fields by the stopped expectation
identities; `deviation_stage_of_variableStoppedChildren` below exhibits the
strategically delicate field and its exact rebased deviation. -/
structure VariableStoppingSuffixCaps
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State) (fuel : ℕ)
    (lowerPotential upperPotential deviationPotential :
      ι → G.HistoryPotential)
    (lowerCharge upperCharge : ι → ℕ → ℝ)
    (deviationCharge :
      ∀ who, G.BehaviorStrategy who → ℕ → ℝ)
    (error : ℝ) where
  horizon : ℕ
  horizon_ge_two : 2 ≤ horizon
  lower_submartingale : ∀ who time, fuel ≤ time →
    G.expectedHistoryValue profile initial
        (lowerPotential who) time ≤
      G.expectedHistoryValue profile initial
        (lowerPotential who) (time + 1)
  lower_stage : ∀ who time, fuel ≤ time →
    G.expectedHistoryValue profile initial
        (lowerPotential who) time ≤
      G.expectedStagePayoff profile initial time who +
        lowerCharge who time
  upper_supermartingale : ∀ who time, fuel ≤ time →
    G.expectedHistoryValue profile initial
        (upperPotential who) (time + 1) ≤
      G.expectedHistoryValue profile initial
        (upperPotential who) time
  upper_stage : ∀ who time, fuel ≤ time →
    G.expectedStagePayoff profile initial time who ≤
      G.expectedHistoryValue profile initial
          (upperPotential who) time +
        upperCharge who time
  deviation_supermartingale :
    ∀ who (deviation : G.BehaviorStrategy who) time, fuel ≤ time →
      G.expectedHistoryValue
          (Function.update profile who deviation) initial
          (deviationPotential who) (time + 1) ≤
        G.expectedHistoryValue
          (Function.update profile who deviation) initial
          (deviationPotential who) time
  deviation_stage :
    ∀ who (deviation : G.BehaviorStrategy who) time, fuel ≤ time →
      G.expectedStagePayoff
          (Function.update profile who deviation) initial time who ≤
        G.expectedHistoryValue
            (Function.update profile who deviation) initial
            (deviationPotential who) time +
          deviationCharge who deviation time
  lower_tail : ∀ who total, horizon ≤ total →
    (total : ℝ)⁻¹ *
        ∑ time ∈ Finset.Ico fuel total, lowerCharge who time ≤ error
  upper_tail : ∀ who total, horizon ≤ total →
    (total : ℝ)⁻¹ *
        ∑ time ∈ Finset.Ico fuel total, upperCharge who time ≤ error
  deviation_tail :
    ∀ who (deviation : G.BehaviorStrategy who) total,
      horizon ≤ total →
        (total : ℝ)⁻¹ *
            ∑ time ∈ Finset.Ico fuel total,
              deviationCharge who deviation time ≤
          error

/-- A first-stopping prefix law and stopped-child suffix caps compose to an
ordinary parent adaptive potential system.  The parent error is exactly the
sum of the amortized bounded-prefix error and the child-tail error. -/
def adaptivePotentialSystemAt_of_variableStopping
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)]
    {profile : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}
    {target : Payoff ι}
    {lowerPotential upperPotential deviationPotential :
      ι → G.HistoryPotential}
    {prefixLowerCharge prefixUpperCharge : ι → ℕ → ℝ}
    {prefixDeviationCharge :
      ∀ who, G.BehaviorStrategy who → ℕ → ℝ}
    {suffixLowerCharge suffixUpperCharge : ι → ℕ → ℝ}
    {suffixDeviationCharge :
      ∀ who, G.BehaviorStrategy who → ℕ → ℝ}
    {prefixError suffixError : ℝ}
    (prefixLaw :
      G.VariableStoppingPrefixLaw profile initial fuel
        lowerPotential upperPotential deviationPotential
        prefixLowerCharge prefixUpperCharge prefixDeviationCharge
        prefixError)
    (suffixCaps :
      G.VariableStoppingSuffixCaps profile initial fuel
        lowerPotential upperPotential deviationPotential
        suffixLowerCharge suffixUpperCharge suffixDeviationCharge
        suffixError)
    (lowerInitial : ∀ who,
      |lowerPotential who 0 (G.emptyHist initial) - target who| ≤
        prefixError + suffixError)
    (upperInitial : ∀ who,
      |upperPotential who 0 (G.emptyHist initial) - target who| ≤
        prefixError + suffixError)
    (deviationInitial : ∀ who,
      |deviationPotential who 0 (G.emptyHist initial) - target who| ≤
        prefixError + suffixError) :
    G.AdaptivePotentialSystemAt profile initial target
      (prefixError + suffixError) where
  horizon := max prefixLaw.horizon (max suffixCaps.horizon fuel)
  lowerPotential := lowerPotential
  upperPotential := upperPotential
  deviationPotential := deviationPotential
  lowerCharge := fun who =>
    prefixThenScalarCharge (fuel := fuel)
      (prefixLowerCharge who) (suffixLowerCharge who)
  upperCharge := fun who =>
    prefixThenScalarCharge (fuel := fuel)
      (prefixUpperCharge who) (suffixUpperCharge who)
  deviationCharge := fun who deviation =>
    prefixThenScalarCharge (fuel := fuel)
      (prefixDeviationCharge who deviation)
      (suffixDeviationCharge who deviation)
  horizon_ge_two :=
    prefixLaw.horizon_ge_two.trans
      (Nat.le_max_left prefixLaw.horizon (max suffixCaps.horizon fuel))
  lower_initial := lowerInitial
  upper_initial := upperInitial
  deviation_initial := deviationInitial
  lower_submartingale := by
    intro who time
    by_cases htime : fuel ≤ time
    · exact suffixCaps.lower_submartingale who time htime
    · exact prefixLaw.lower_submartingale who time
        (Nat.lt_of_not_ge htime)
  lower_stage := by
    intro who time
    by_cases htime : fuel ≤ time
    · simpa [prefixThenScalarCharge, htime] using
        suffixCaps.lower_stage who time htime
    · simpa [prefixThenScalarCharge, htime] using
        prefixLaw.lower_stage who time (Nat.lt_of_not_ge htime)
  upper_supermartingale := by
    intro who time
    by_cases htime : fuel ≤ time
    · exact suffixCaps.upper_supermartingale who time htime
    · exact prefixLaw.upper_supermartingale who time
        (Nat.lt_of_not_ge htime)
  upper_stage := by
    intro who time
    by_cases htime : fuel ≤ time
    · simpa [prefixThenScalarCharge, htime] using
        suffixCaps.upper_stage who time htime
    · simpa [prefixThenScalarCharge, htime] using
        prefixLaw.upper_stage who time (Nat.lt_of_not_ge htime)
  deviation_supermartingale := by
    intro who deviation time
    by_cases htime : fuel ≤ time
    · exact suffixCaps.deviation_supermartingale who deviation time htime
    · exact prefixLaw.deviation_supermartingale who deviation time
        (Nat.lt_of_not_ge htime)
  deviation_stage := by
    intro who deviation time
    by_cases htime : fuel ≤ time
    · simpa [prefixThenScalarCharge, htime] using
        suffixCaps.deviation_stage who deviation time htime
    · simpa [prefixThenScalarCharge, htime] using
        prefixLaw.deviation_stage who deviation time
          (Nat.lt_of_not_ge htime)
  lower_charge_cesaro := by
    intro who total htotal
    apply normalized_prefixThenScalarCharge_le
      (prefixCost := prefixLaw.prefixCost)
      (prefixError := prefixError) (suffixError := suffixError)
    · exact le_trans
        (Nat.le_max_right suffixCaps.horizon fuel)
        (le_trans (Nat.le_max_right prefixLaw.horizon _) htotal)
    · exact prefixLaw.lower_prefix_cost who
    · exact prefixLaw.amortized total
        (le_trans (Nat.le_max_left prefixLaw.horizon _) htotal)
    · exact suffixCaps.lower_tail who total
        (le_trans
          (Nat.le_max_left suffixCaps.horizon fuel)
          (le_trans (Nat.le_max_right prefixLaw.horizon _) htotal))
  upper_charge_cesaro := by
    intro who total htotal
    apply normalized_prefixThenScalarCharge_le
      (prefixCost := prefixLaw.prefixCost)
      (prefixError := prefixError) (suffixError := suffixError)
    · exact le_trans
        (Nat.le_max_right suffixCaps.horizon fuel)
        (le_trans (Nat.le_max_right prefixLaw.horizon _) htotal)
    · exact prefixLaw.upper_prefix_cost who
    · exact prefixLaw.amortized total
        (le_trans (Nat.le_max_left prefixLaw.horizon _) htotal)
    · exact suffixCaps.upper_tail who total
        (le_trans
          (Nat.le_max_left suffixCaps.horizon fuel)
          (le_trans (Nat.le_max_right prefixLaw.horizon _) htotal))
  deviation_charge_cesaro := by
    intro who deviation total htotal
    apply normalized_prefixThenScalarCharge_le
      (prefixCost := prefixLaw.prefixCost)
      (prefixError := prefixError) (suffixError := suffixError)
    · exact le_trans
        (Nat.le_max_right suffixCaps.horizon fuel)
        (le_trans (Nat.le_max_right prefixLaw.horizon _) htotal)
    · exact prefixLaw.deviation_prefix_cost who deviation
    · exact prefixLaw.amortized total
        (le_trans (Nat.le_max_left prefixLaw.horizon _) htotal)
    · exact suffixCaps.deviation_tail who deviation total
        (le_trans
          (Nat.le_max_left suffixCaps.horizon fuel)
          (le_trans (Nat.le_max_right prefixLaw.horizon _) htotal))

/-- Certificate-level form of the variable-stopping composition. -/
theorem isAdaptivePotentialCertificateAt_of_variableStopping
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)]
    {profile : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}
    {target : Payoff ι}
    {lowerPotential upperPotential deviationPotential :
      ι → G.HistoryPotential}
    {prefixLowerCharge prefixUpperCharge : ι → ℕ → ℝ}
    {prefixDeviationCharge :
      ∀ who, G.BehaviorStrategy who → ℕ → ℝ}
    {suffixLowerCharge suffixUpperCharge : ι → ℕ → ℝ}
    {suffixDeviationCharge :
      ∀ who, G.BehaviorStrategy who → ℕ → ℝ}
    {prefixError suffixError : ℝ}
    (prefixLaw :
      G.VariableStoppingPrefixLaw profile initial fuel
        lowerPotential upperPotential deviationPotential
        prefixLowerCharge prefixUpperCharge prefixDeviationCharge
        prefixError)
    (suffixCaps :
      G.VariableStoppingSuffixCaps profile initial fuel
        lowerPotential upperPotential deviationPotential
        suffixLowerCharge suffixUpperCharge suffixDeviationCharge
        suffixError)
    (lowerInitial : ∀ who,
      |lowerPotential who 0 (G.emptyHist initial) - target who| ≤
        prefixError + suffixError)
    (upperInitial : ∀ who,
      |upperPotential who 0 (G.emptyHist initial) - target who| ≤
        prefixError + suffixError)
    (deviationInitial : ∀ who,
      |deviationPotential who 0 (G.emptyHist initial) - target who| ≤
        prefixError + suffixError) :
    G.IsAdaptivePotentialCertificateAt initial target
      (prefixError + suffixError) :=
  (G.adaptivePotentialSystemAt_of_variableStopping
    prefixLaw suffixCaps lowerInitial upperInitial
    deviationInitial).toIsAdaptivePotentialCertificateAt

namespace FiniteChildAdaptivePotentialFamily

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {childError suffixError : ℝ}

private theorem expect_mono_on_support
    {α : Type} [Finite α]
    (law : PMF α) (f g : α → ℝ)
    (hfg : ∀ x ∈ law.support, f x ≤ g x) :
    expect law f ≤ expect law g := by
  classical
  let patched : α → ℝ :=
    fun x => if law x = 0 then g x else f x
  calc
    expect law f = expect law patched := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro x hx
      have hx0 : law x ≠ 0 := by
        simpa [PMF.mem_support_iff] using hx
      simp [patched, hx0]
    _ ≤ expect law g := by
      apply expect_mono
      intro x
      by_cases hx : law x = 0
      · simp [patched, hx]
      · simp only [patched, hx, ↓reduceIte]
        exact hfg x (by simpa [PMF.mem_support_iff])

/-- The post-stopping deviation stage bound uses the restriction of the
single root deviation, not a separately chosen child deviation. -/
theorem deviation_stage_of_variableStoppedChildren
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    {fuel time : ℕ}
    (rule : G.OnlineCausalBoundedStoppingRule fuel)
    (selection : G.BehaviorProfile) (initial : G.State)
    (observe : G.BoundedStoppedHistory fuel → Child)
    (hentry : ∀ base : G.BoundedStoppedHistory fuel,
      base.2.2 = entry (observe base))
    (prefixPotential : ι → G.HistoryPotential)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (htime : fuel ≤ time) :
    G.expectedStagePayoff
        (Function.update
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          who deviation)
        initial time who ≤
      G.expectedHistoryValue
          (Function.update
            (G.causalTerminalChildDispatcher rule selection
              (family.observedStoppedProfile observe))
            who deviation)
          initial
          (G.prefixThenStoppedChildHistoryPotential rule.selector
            (prefixPotential who)
            (family.stoppedDeviationPotential observe who))
          time +
        G.stoppedChildDeviationScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector
          (family.stoppedDeviationCharge observe)
          who deviation time := by
  let profile :=
    G.causalTerminalChildDispatcher rule selection
      (family.observedStoppedProfile observe)
  let updated := Function.update profile who deviation
  have joint :
      G.CausalDispatcherJointLawAt
        updated initial rule.selector htime :=
    G.causalDispatcherJointLawAt_of_causal
      updated initial rule.selector rule.causal htime
  have hdisintegration :
      G.IsRootStoppedSuffixDisintegration
        updated initial rule.selector htime :=
    jointToDisintegration updated initial rule.selector
      rule.causal htime joint
  rw [G.expectedStagePayoff_eq_stoppedSuffix
    updated initial rule.selector htime hdisintegration who]
  rw [G.expectedHistoryValue_prefixThenStoppedChild_eq
    updated initial rule.selector (prefixPotential who)
    (family.stoppedDeviationPotential observe who)
    htime joint]
  unfold stoppedChildDeviationScalarCharge
  rw [← expect_add]
  apply expect_mono_on_support
  intro base hbase
  have hoccurs :=
    rule.occurs_of_mem_stoppedHistoryLaw
      updated initial base hbase
  rw [G.afterHistoryProfile_update,
    G.afterHistoryProfile_causalTerminalChildDispatcher_canonical]
  rw [
    G.expectedStagePayoff_update_canonicalCausalStoppedChildProfile
      rule selection (family.observedStoppedProfile observe)
      base hoccurs who deviation,
    G.expectedHistoryValue_update_canonicalCausalStoppedChildProfile
      rule selection (family.observedStoppedProfile observe)
      base hoccurs who deviation
  ]
  rw [hentry base]
  exact
    (family.system (observe base)).deviation_stage
      who (G.afterHistoryStrategy deviation base.2)
      (time - base.1.val)

/-- Exact stopped-suffix laws and the common-root child charge tail produce
all post-fuel caps required by the parent composition theorem. -/
def variableStoppingSuffixCaps
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    {fuel : ℕ}
    (rule : G.OnlineCausalBoundedStoppingRule fuel)
    (selection : G.BehaviorProfile) (initial : G.State)
    (observe : G.BoundedStoppedHistory fuel → Child)
    (hentry : ∀ base : G.BoundedStoppedHistory fuel,
      base.2.2 = entry (observe base))
    (prefixLower prefixUpper prefixDeviation :
      ι → G.HistoryPotential)
    (tail :
      G.CommonRootChildChargeTailBound
        (G.causalTerminalChildDispatcher rule selection
          (family.observedStoppedProfile observe))
        initial rule.selector
        (family.stoppedLowerCharge observe)
        (family.stoppedUpperCharge observe)
        (family.stoppedDeviationCharge observe) suffixError) :
    G.VariableStoppingSuffixCaps
      (G.causalTerminalChildDispatcher rule selection
        (family.observedStoppedProfile observe))
      initial fuel
      (fun who =>
        G.prefixThenStoppedChildHistoryPotential rule.selector
          (prefixLower who) (family.stoppedLowerPotential observe who))
      (fun who =>
        G.prefixThenStoppedChildHistoryPotential rule.selector
          (prefixUpper who) (family.stoppedUpperPotential observe who))
      (fun who =>
        G.prefixThenStoppedChildHistoryPotential rule.selector
          (prefixDeviation who)
          (family.stoppedDeviationPotential observe who))
      (fun who rootTime =>
        G.stoppedChildScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector (family.stoppedLowerCharge observe)
          who rootTime)
      (fun who rootTime =>
        G.stoppedChildScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector (family.stoppedUpperCharge observe)
          who rootTime)
      (fun who deviation rootTime =>
        G.stoppedChildDeviationScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector
          (family.stoppedDeviationCharge observe)
          who deviation rootTime)
      suffixError := by
  let profile :=
    G.causalTerminalChildDispatcher rule selection
      (family.observedStoppedProfile observe)
  have joint : ∀ total (htotal : fuel ≤ total),
      G.CausalDispatcherJointLawAt
        profile initial rule.selector htotal := by
    intro total htotal
    exact G.causalDispatcherJointLawAt_of_causal
      profile initial rule.selector rule.causal htotal
  have deviationJoint :
      ∀ who (deviation : G.BehaviorStrategy who)
        total (htotal : fuel ≤ total),
        G.CausalDispatcherJointLawAt
          (Function.update profile who deviation)
          initial rule.selector htotal := by
    intro who deviation total htotal
    exact G.causalDispatcherJointLawAt_of_causal
      (Function.update profile who deviation)
      initial rule.selector rule.causal htotal
  refine {
    horizon := tail.horizon
    horizon_ge_two := tail.horizon_ge_two
    lower_submartingale := ?_
    lower_stage := ?_
    upper_supermartingale := ?_
    upper_stage := ?_
    deviation_supermartingale := ?_
    deviation_stage := ?_
    lower_tail := ?_
    upper_tail := ?_
    deviation_tail := ?_
  }
  · intro who time htime
    rw [G.expectedHistoryValue_prefixThenStoppedChild_eq
      profile initial rule.selector (prefixLower who)
      (family.stoppedLowerPotential observe who)
      htime (joint time htime)]
    have hnext : fuel ≤ time + 1 := le_trans htime (Nat.le_succ time)
    rw [G.expectedHistoryValue_prefixThenStoppedChild_eq
      profile initial rule.selector (prefixLower who)
      (family.stoppedLowerPotential observe who)
      hnext (joint (time + 1) hnext)]
    apply expect_mono_on_support
    intro base hbaseSupport
    have hoccurs :=
      rule.occurs_of_mem_stoppedHistoryLaw
        profile initial base hbaseSupport
    have hbase : base.1.val ≤ time :=
      le_trans (Nat.lt_succ_iff.mp base.1.isLt) htime
    have hsub :
        time + 1 - base.1.val = time - base.1.val + 1 := by
      omega
    rw [
      G.afterHistoryProfile_causalTerminalChildDispatcher_canonical,
      G.expectedHistoryValue_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs,
      G.expectedHistoryValue_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs
    ]
    rw [hentry base]
    simpa only [hsub, observedStoppedProfile,
      stoppedLowerPotential] using
      (family.system (observe base)).lower_submartingale
        who (time - base.1.val)
  · intro who time htime
    have hdisintegration :=
      jointToDisintegration profile initial rule.selector
        rule.causal htime (joint time htime)
    rw [G.expectedHistoryValue_prefixThenStoppedChild_eq
      profile initial rule.selector (prefixLower who)
      (family.stoppedLowerPotential observe who)
      htime (joint time htime)]
    rw [G.expectedStagePayoff_eq_stoppedSuffix
      profile initial rule.selector htime hdisintegration who]
    unfold stoppedChildScalarCharge
    rw [← expect_add]
    apply expect_mono_on_support
    intro base hbaseSupport
    have hoccurs :=
      rule.occurs_of_mem_stoppedHistoryLaw
        profile initial base hbaseSupport
    have hbase : base.1.val ≤ time :=
      le_trans (Nat.lt_succ_iff.mp base.1.isLt) htime
    rw [
      G.afterHistoryProfile_causalTerminalChildDispatcher_canonical,
      G.expectedHistoryValue_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs,
      G.expectedStagePayoff_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs
    ]
    rw [hentry base]
    exact
      (family.system (observe base)).lower_stage
        who (time - base.1.val)
  · intro who time htime
    have hnext : fuel ≤ time + 1 := le_trans htime (Nat.le_succ time)
    rw [G.expectedHistoryValue_prefixThenStoppedChild_eq
      profile initial rule.selector (prefixUpper who)
      (family.stoppedUpperPotential observe who)
      hnext (joint (time + 1) hnext)]
    rw [G.expectedHistoryValue_prefixThenStoppedChild_eq
      profile initial rule.selector (prefixUpper who)
      (family.stoppedUpperPotential observe who)
      htime (joint time htime)]
    apply expect_mono_on_support
    intro base hbaseSupport
    have hoccurs :=
      rule.occurs_of_mem_stoppedHistoryLaw
        profile initial base hbaseSupport
    have hbase : base.1.val ≤ time :=
      le_trans (Nat.lt_succ_iff.mp base.1.isLt) htime
    have hsub :
        time + 1 - base.1.val = time - base.1.val + 1 := by
      omega
    rw [
      G.afterHistoryProfile_causalTerminalChildDispatcher_canonical,
      G.expectedHistoryValue_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs,
      G.expectedHistoryValue_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs
    ]
    rw [hentry base]
    simpa only [hsub, observedStoppedProfile,
      stoppedUpperPotential] using
      (family.system (observe base)).upper_supermartingale
        who (time - base.1.val)
  · intro who time htime
    have hdisintegration :=
      jointToDisintegration profile initial rule.selector
        rule.causal htime (joint time htime)
    rw [G.expectedStagePayoff_eq_stoppedSuffix
      profile initial rule.selector htime hdisintegration who]
    rw [G.expectedHistoryValue_prefixThenStoppedChild_eq
      profile initial rule.selector (prefixUpper who)
      (family.stoppedUpperPotential observe who)
      htime (joint time htime)]
    unfold stoppedChildScalarCharge
    rw [← expect_add]
    apply expect_mono_on_support
    intro base hbaseSupport
    have hoccurs :=
      rule.occurs_of_mem_stoppedHistoryLaw
        profile initial base hbaseSupport
    rw [
      G.afterHistoryProfile_causalTerminalChildDispatcher_canonical,
      G.expectedStagePayoff_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs,
      G.expectedHistoryValue_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs
    ]
    rw [hentry base]
    exact
      (family.system (observe base)).upper_stage
        who (time - base.1.val)
  · intro who deviation time htime
    let updated := Function.update profile who deviation
    have hnext : fuel ≤ time + 1 := le_trans htime (Nat.le_succ time)
    rw [G.expectedHistoryValue_prefixThenStoppedChild_eq
      updated initial rule.selector (prefixDeviation who)
      (family.stoppedDeviationPotential observe who)
      hnext (deviationJoint who deviation (time + 1) hnext)]
    rw [G.expectedHistoryValue_prefixThenStoppedChild_eq
      updated initial rule.selector (prefixDeviation who)
      (family.stoppedDeviationPotential observe who)
      htime (deviationJoint who deviation time htime)]
    apply expect_mono_on_support
    intro base hbaseSupport
    have hoccurs :=
      rule.occurs_of_mem_stoppedHistoryLaw
        (Function.update profile who deviation)
        initial base hbaseSupport
    have hbase : base.1.val ≤ time :=
      le_trans (Nat.lt_succ_iff.mp base.1.isLt) htime
    have hsub :
        time + 1 - base.1.val = time - base.1.val + 1 := by
      omega
    rw [G.afterHistoryProfile_update,
      G.afterHistoryProfile_causalTerminalChildDispatcher_canonical]
    rw [
      G.expectedHistoryValue_update_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs who deviation,
      G.expectedHistoryValue_update_canonicalCausalStoppedChildProfile
        rule selection (family.observedStoppedProfile observe)
        base hoccurs who deviation
    ]
    rw [hentry base]
    simpa only [hsub, observedStoppedProfile,
      stoppedDeviationPotential] using
      (family.system (observe base)).deviation_supermartingale
        who (G.afterHistoryStrategy deviation base.2)
        (time - base.1.val)
  · intro who deviation time htime
    exact family.deviation_stage_of_variableStoppedChildren
      rule selection initial observe hentry prefixDeviation
      who deviation htime
  · intro who total htotal
    exact tail.lower who total htotal
  · intro who total htotal
    exact tail.upper who total htotal
  · intro who deviation total htotal
    exact tail.deviation who deviation total htotal

end FiniteChildAdaptivePotentialFamily

end StochasticGame
end GameTheory
