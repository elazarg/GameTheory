/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FiniteAdaptiveChildChargeLowerBound
import GameTheory.Concepts.Stochastic.PublicVariableStoppingAdaptiveDispatcher

/-!
# Local compiler for a variable-stopping prefix law

The abstract `VariableStoppingPrefixLaw` stores expectation inequalities.
This file derives those inequalities from historywise Bellman conditions on
the support of the actual prescribed or deviating history law.

Stopping can happen strictly before the common fuel horizon.  Accordingly,
`onlineSwitchHistoryPotential` changes from a selecting potential to the
selected child's potential as soon as the online stopping view returns a
stopped path.  The local hypotheses below apply to the resulting potential
under the actual dynamic dispatcher; they include histories where a child is
already active although calendar time is still below `fuel`.

The compiler also replaces the three cumulative charge assumptions and the
amortization assumption by one uniform pointwise charge bound.  Its prefix
cost is exactly `fuel * chargeBound`, and a ceiling formula chooses an
explicit horizon for every positive requested error.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- Follow the selecting potential before online stopping and the realized
child potential immediately afterwards. -/
def onlineSwitchHistoryPotential {fuel : ℕ}
    (rule : G.OnlineCausalBoundedStoppingRule fuel)
    (selecting : G.HistoryPotential)
    (child : G.BoundedStoppedHistory fuel → G.HistoryPotential) :
    G.HistoryPotential :=
  fun time history =>
    match rule.view time history with
    | none => selecting time history
    | some path =>
        child path.base path.suffixLength path.suffix

@[simp] theorem onlineSwitchHistoryPotential_appendHist
    {fuel suffixLength : ℕ}
    (rule : G.OnlineCausalBoundedStoppingRule fuel)
    (selecting : G.HistoryPotential)
    (child : G.BoundedStoppedHistory fuel → G.HistoryPotential)
    (base : G.BoundedStoppedHistory fuel)
    (hoccurs : G.OnlineStoppedBaseOccurs rule.view base)
    (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2.2) :
    G.onlineSwitchHistoryPotential rule selecting child
        (base.1.val + suffixLength) (G.appendHist base.2 suffix) =
      child base suffixLength suffix := by
  simp only [onlineSwitchHistoryPotential,
    rule.persistent base hoccurs suffix hstart]
  rfl

/-- The repaired online-rule API agrees after `fuel` with the root
decomposition used by stopped-suffix expectations. -/
def IsRootStoppedPathViewCompatible {fuel : ℕ}
    (rule : G.OnlineCausalBoundedStoppingRule fuel) : Prop :=
  ∀ time (htime : fuel ≤ time) (history : G.Hist time),
    rule.view time history =
      some
        (G.rootOnlineStoppedPathOfHistory
          rule.selector htime history)

/-- Root stopped-path view compatibility is now a theorem of every sound
online rule, rather than an unrelated composition premise. -/
theorem OnlineCausalBoundedStoppingRule.isRootStoppedPathViewCompatible
    {fuel : ℕ}
    (rule : G.OnlineCausalBoundedStoppingRule fuel) :
    G.IsRootStoppedPathViewCompatible rule :=
  rule.complete

/-- Once the online view and root decomposition agree after `fuel`, wrapping
an immediately switched potential in the old fuel switch changes nothing. -/
theorem prefixThenStoppedChild_onlineSwitch_eq
    {fuel : ℕ}
    (rule : G.OnlineCausalBoundedStoppingRule fuel)
    (selecting : G.HistoryPotential)
    (child : G.BoundedStoppedHistory fuel → G.HistoryPotential) :
    G.prefixThenStoppedChildHistoryPotential rule.selector
        (G.onlineSwitchHistoryPotential rule selecting child) child =
      G.onlineSwitchHistoryPotential rule selecting child := by
  funext time history
  by_cases htime : fuel ≤ time
  · simp only [prefixThenStoppedChildHistoryPotential, dif_pos htime,
      onlineSwitchHistoryPotential,
      rule.isRootStoppedPathViewCompatible time htime history]
    rfl
  · simp only [prefixThenStoppedChildHistoryPotential, dif_neg htime]

/-- Turn a historywise charge into the scalar charge consumed by an adaptive
potential system. -/
def expectedHistoryCharge
    [Fintype ι]
    (profile : G.BehaviorProfile) (initial : G.State)
    (charge : G.HistoryPotential) (time : ℕ) : ℝ :=
  G.expectedHistoryValue profile initial charge time

/-- The exact finite prefix bill produced by a uniform historywise bound. -/
def variableStoppingPrefixCost
    (fuel : ℕ) (chargeBound : ℝ) : ℝ :=
  (fuel : ℝ) * chargeBound

/-- An explicit horizon after which the fixed prefix bill is at most
`error` per stage. -/
def variableStoppingPrefixHorizon
    (fuel : ℕ) (chargeBound error : ℝ) : ℕ :=
  max 2 ⌈variableStoppingPrefixCost fuel chargeBound / error⌉₊

private theorem expect_le_of_le_on_support
    {α : Type} [Finite α]
    (law : PMF α) (f g : α → ℝ)
    (hfg : ∀ x ∈ law.support, f x ≤ g x) :
    expect law f ≤ expect law g := by
  classical
  let patched : α → ℝ :=
    fun x => if law x = 0 then g x else f x
  calc
    expect law f = expect law patched := by
      apply expect_congr_on_support
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

/-- Local, support-sensitive assumptions sufficient for the complete
expectation-level prefix law.

The deviation fields quantify over the single root unilateral deviation and
use its actual history support.  Thus the constructor does not assume that a
player is unable to affect the payoff or child continuation after stopping;
that strategic burden is visible in the two local deviation inequalities. -/
structure PointwiseVariableStoppingPrefixData
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State) (fuel : ℕ)
    (lowerPotential upperPotential deviationPotential :
      ι → G.HistoryPotential)
    (lowerHistoryCharge upperHistoryCharge : ι → G.HistoryPotential)
    (deviationHistoryCharge :
      ∀ who, G.BehaviorStrategy who → G.HistoryPotential) where
  region : G.FinitePublicCoinStoppingRegion
  rank_le_fuel : region.rank initial ≤ fuel
  chargeBound : ℝ
  chargeBound_nonneg : 0 ≤ chargeBound
  lower_drift :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        lowerPotential who time history ≤
          G.historyContinuationEU profile
            (lowerPotential who) history
  lower_stage :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        lowerPotential who time history ≤
          G.stageEUAt profile history who +
            lowerHistoryCharge who time history
  upper_drift :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        G.historyContinuationEU profile
            (upperPotential who) history ≤
          upperPotential who time history
  upper_stage :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        G.stageEUAt profile history who ≤
          upperPotential who time history +
            upperHistoryCharge who time history
  deviation_drift :
    ∀ who (deviation : G.BehaviorStrategy who) time,
      time < fuel →
        ∀ history ∈
            (G.histDist
              (Function.update profile who deviation)
              initial time).support,
          G.historyContinuationEU
              (Function.update profile who deviation)
              (deviationPotential who) history ≤
            deviationPotential who time history
  deviation_stage :
    ∀ who (deviation : G.BehaviorStrategy who) time,
      time < fuel →
        ∀ history ∈
            (G.histDist
              (Function.update profile who deviation)
              initial time).support,
          G.stageEUAt
              (Function.update profile who deviation)
              history who ≤
            deviationPotential who time history +
              deviationHistoryCharge who deviation time history
  lower_charge_le :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        lowerHistoryCharge who time history ≤ chargeBound
  upper_charge_le :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        upperHistoryCharge who time history ≤ chargeBound
  deviation_charge_le :
    ∀ who (deviation : G.BehaviorStrategy who) time,
      time < fuel →
        ∀ history ∈
            (G.histDist
              (Function.update profile who deviation)
              initial time).support,
          deviationHistoryCharge who deviation time history ≤ chargeBound

namespace PointwiseVariableStoppingPrefixData

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)]
  {profile : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}
  {lowerPotential upperPotential deviationPotential :
    ι → G.HistoryPotential}
  {lowerHistoryCharge upperHistoryCharge : ι → G.HistoryPotential}
  {deviationHistoryCharge :
    ∀ who, G.BehaviorStrategy who → G.HistoryPotential}

/-- Every prescribed lower prefix charge has the explicit finite bill. -/
theorem sum_expectedLowerCharge_le
    (data :
      G.PointwiseVariableStoppingPrefixData profile initial fuel
        lowerPotential upperPotential deviationPotential
        lowerHistoryCharge upperHistoryCharge deviationHistoryCharge)
    (who : ι) :
    ∑ time ∈ Finset.range fuel,
        G.expectedHistoryCharge profile initial
          (lowerHistoryCharge who) time ≤
      variableStoppingPrefixCost fuel data.chargeBound := by
  calc
    ∑ time ∈ Finset.range fuel,
        G.expectedHistoryCharge profile initial
          (lowerHistoryCharge who) time ≤
      ∑ _time ∈ Finset.range fuel, data.chargeBound := by
        apply Finset.sum_le_sum
        intro time htime
        unfold expectedHistoryCharge expectedHistoryValue
        simpa only [expect_const] using
          expect_le_of_le_on_support
            (G.histDist profile initial time)
            (lowerHistoryCharge who time)
            (fun _ => data.chargeBound)
            (data.lower_charge_le who time
              (Finset.mem_range.mp htime))
    _ = variableStoppingPrefixCost fuel data.chargeBound := by
      simp [variableStoppingPrefixCost]

/-- Every prescribed upper prefix charge has the explicit finite bill. -/
theorem sum_expectedUpperCharge_le
    (data :
      G.PointwiseVariableStoppingPrefixData profile initial fuel
        lowerPotential upperPotential deviationPotential
        lowerHistoryCharge upperHistoryCharge deviationHistoryCharge)
    (who : ι) :
    ∑ time ∈ Finset.range fuel,
        G.expectedHistoryCharge profile initial
          (upperHistoryCharge who) time ≤
      variableStoppingPrefixCost fuel data.chargeBound := by
  calc
    ∑ time ∈ Finset.range fuel,
        G.expectedHistoryCharge profile initial
          (upperHistoryCharge who) time ≤
      ∑ _time ∈ Finset.range fuel, data.chargeBound := by
        apply Finset.sum_le_sum
        intro time htime
        unfold expectedHistoryCharge expectedHistoryValue
        simpa only [expect_const] using
          expect_le_of_le_on_support
            (G.histDist profile initial time)
            (upperHistoryCharge who time)
            (fun _ => data.chargeBound)
            (data.upper_charge_le who time
              (Finset.mem_range.mp htime))
    _ = variableStoppingPrefixCost fuel data.chargeBound := by
      simp [variableStoppingPrefixCost]

/-- Every unilateral-deviation prefix charge has the same explicit bill. -/
theorem sum_expectedDeviationCharge_le
    (data :
      G.PointwiseVariableStoppingPrefixData profile initial fuel
        lowerPotential upperPotential deviationPotential
        lowerHistoryCharge upperHistoryCharge deviationHistoryCharge)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    ∑ time ∈ Finset.range fuel,
        G.expectedHistoryCharge
          (Function.update profile who deviation) initial
          (deviationHistoryCharge who deviation) time ≤
      variableStoppingPrefixCost fuel data.chargeBound := by
  calc
    ∑ time ∈ Finset.range fuel,
        G.expectedHistoryCharge
          (Function.update profile who deviation) initial
          (deviationHistoryCharge who deviation) time ≤
      ∑ _time ∈ Finset.range fuel, data.chargeBound := by
        apply Finset.sum_le_sum
        intro time htime
        unfold expectedHistoryCharge expectedHistoryValue
        simpa only [expect_const] using
          expect_le_of_le_on_support
            (G.histDist
              (Function.update profile who deviation) initial time)
            (deviationHistoryCharge who deviation time)
            (fun _ => data.chargeBound)
            (data.deviation_charge_le who deviation time
              (Finset.mem_range.mp htime))
    _ = variableStoppingPrefixCost fuel data.chargeBound := by
      simp [variableStoppingPrefixCost]

/-- The ceiling horizon amortizes the exact finite prefix bill at every later
horizon. -/
theorem amortized_prefixCost_le
    (data :
      G.PointwiseVariableStoppingPrefixData profile initial fuel
        lowerPotential upperPotential deviationPotential
        lowerHistoryCharge upperHistoryCharge deviationHistoryCharge)
    {error : ℝ} (herror : 0 < error)
    {total : ℕ}
    (htotal :
      variableStoppingPrefixHorizon
          fuel data.chargeBound error ≤ total) :
    (total : ℝ)⁻¹ *
        variableStoppingPrefixCost fuel data.chargeBound ≤ error := by
  have hcost :
      0 ≤ variableStoppingPrefixCost fuel data.chargeBound := by
    exact mul_nonneg (Nat.cast_nonneg fuel) data.chargeBound_nonneg
  have hceil :
      variableStoppingPrefixCost fuel data.chargeBound / error ≤
        (⌈variableStoppingPrefixCost fuel data.chargeBound / error⌉₊ :
          ℝ) :=
    Nat.le_ceil _
  have hceilTotal :
      (⌈variableStoppingPrefixCost fuel data.chargeBound / error⌉₊ :
          ℝ) ≤ total := by
    exact_mod_cast
      le_trans
        (Nat.le_max_right 2
          ⌈variableStoppingPrefixCost fuel data.chargeBound / error⌉₊)
        htotal
  have hcostTotal :
      variableStoppingPrefixCost fuel data.chargeBound ≤
        (total : ℝ) * error := by
    apply (div_le_iff₀ herror).mp
    exact hceil.trans hceilTotal
  have htotalPos : (0 : ℝ) < total := by
    have : 2 ≤ total :=
      le_trans
        (Nat.le_max_left 2
          ⌈variableStoppingPrefixCost fuel data.chargeBound / error⌉₊)
        htotal
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) this)
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ htotalPos).2 (by
    simpa [mul_comm] using hcostTotal)

/-- Compile support-sensitive local Bellman data into the full abstract
variable-stopping prefix law.

There is no separate cumulative-budget or horizon input: both are computed
from `fuel`, `chargeBound`, and the requested positive `error`. -/
def toVariableStoppingPrefixLaw
    (data :
      G.PointwiseVariableStoppingPrefixData profile initial fuel
        lowerPotential upperPotential deviationPotential
        lowerHistoryCharge upperHistoryCharge deviationHistoryCharge)
    (error : ℝ) (herror : 0 < error) :
    G.VariableStoppingPrefixLaw profile initial fuel
      lowerPotential upperPotential deviationPotential
      (fun who =>
        G.expectedHistoryCharge profile initial
          (lowerHistoryCharge who))
      (fun who =>
        G.expectedHistoryCharge profile initial
          (upperHistoryCharge who))
      (fun who deviation =>
        G.expectedHistoryCharge
          (Function.update profile who deviation) initial
          (deviationHistoryCharge who deviation))
      error where
  region := data.region
  rank_le_fuel := data.rank_le_fuel
  horizon :=
    variableStoppingPrefixHorizon fuel data.chargeBound error
  prefixCost :=
    variableStoppingPrefixCost fuel data.chargeBound
  horizon_ge_two := Nat.le_max_left _ _
  lower_submartingale := by
    intro who time htime
    rw [G.expectedHistoryValue_succ]
    unfold expectedHistoryValue
    exact expect_le_of_le_on_support
      (G.histDist profile initial time)
      (lowerPotential who time)
      (fun history =>
        G.historyContinuationEU profile
          (lowerPotential who) history)
      (data.lower_drift who time htime)
  lower_stage := by
    intro who time htime
    unfold expectedHistoryCharge expectedHistoryValue
      expectedStagePayoff
    rw [← expect_add]
    exact expect_le_of_le_on_support
      (G.histDist profile initial time)
      (lowerPotential who time)
      (fun history =>
        G.stageEUAt profile history who +
          lowerHistoryCharge who time history)
      (data.lower_stage who time htime)
  upper_supermartingale := by
    intro who time htime
    rw [G.expectedHistoryValue_succ]
    unfold expectedHistoryValue
    exact expect_le_of_le_on_support
      (G.histDist profile initial time)
      (fun history =>
        G.historyContinuationEU profile
          (upperPotential who) history)
      (upperPotential who time)
      (data.upper_drift who time htime)
  upper_stage := by
    intro who time htime
    unfold expectedHistoryCharge expectedHistoryValue
      expectedStagePayoff
    rw [← expect_add]
    exact expect_le_of_le_on_support
      (G.histDist profile initial time)
      (fun history => G.stageEUAt profile history who)
      (fun history =>
        upperPotential who time history +
          upperHistoryCharge who time history)
      (data.upper_stage who time htime)
  deviation_supermartingale := by
    intro who deviation time htime
    rw [G.expectedHistoryValue_succ]
    unfold expectedHistoryValue
    exact expect_le_of_le_on_support
      (G.histDist
        (Function.update profile who deviation) initial time)
      (fun history =>
        G.historyContinuationEU
          (Function.update profile who deviation)
          (deviationPotential who) history)
      (deviationPotential who time)
      (data.deviation_drift who deviation time htime)
  deviation_stage := by
    intro who deviation time htime
    unfold expectedHistoryCharge expectedHistoryValue
      expectedStagePayoff
    rw [← expect_add]
    exact expect_le_of_le_on_support
      (G.histDist
        (Function.update profile who deviation) initial time)
      (fun history =>
        G.stageEUAt
          (Function.update profile who deviation) history who)
      (fun history =>
        deviationPotential who time history +
          deviationHistoryCharge who deviation time history)
      (data.deviation_stage who deviation time htime)
  lower_prefix_cost := data.sum_expectedLowerCharge_le
  upper_prefix_cost := data.sum_expectedUpperCharge_le
  deviation_prefix_cost :=
    data.sum_expectedDeviationCharge_le
  amortized := by
    intro total htotal
    exact data.amortized_prefixCost_le herror htotal

end PointwiseVariableStoppingPrefixData

/-- Canonical one-stage charge: the absolute gap between the current mixed
payoff and a history potential. -/
def historyPotentialGapCharge
    [Fintype ι]
    (profile : G.BehaviorProfile) (who : ι)
    (potential : G.HistoryPotential) :
    G.HistoryPotential :=
  fun time history =>
    |G.stageEUAt profile history who - potential time history|

/-- A finite payoff bound controls every behaviorally mixed stage payoff. -/
theorem abs_stageEUAt_le_of_abs_payoff_le
    [Fintype ι]
    (profile : G.BehaviorProfile) {payoffBound : ℝ}
    (hpayoff :
      ∀ state action who,
        |G.stagePayoff state action who| ≤ payoffBound)
    {time : ℕ} (history : G.Hist time) (who : ι) :
    |G.stageEUAt profile history who| ≤ payoffBound := by
  unfold stageEUAt
  exact abs_expect_le_of_abs_le _ _
    (fun action => hpayoff history.2 action who)

/-- The reduced local input for a bounded variable-stopping prefix.

The only dynamic assumptions are sub/superharmonicity on supported root
histories, under the prescribed profile and every one-player update.
Uniform payoff and potential bounds generate canonical absolute-gap charges,
all stage inequalities, the finite prefix bill, and its amortization. -/
structure BoundedVariableStoppingPrefixPotentials
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State) (fuel : ℕ)
    (lowerPotential upperPotential deviationPotential :
      ι → G.HistoryPotential) where
  region : G.FinitePublicCoinStoppingRegion
  rank_le_fuel : region.rank initial ≤ fuel
  payoffBound : ℝ
  potentialBound : ℝ
  payoffBound_nonneg : 0 ≤ payoffBound
  potentialBound_nonneg : 0 ≤ potentialBound
  payoff_abs :
    ∀ state action who,
      |G.stagePayoff state action who| ≤ payoffBound
  lower_potential_abs :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        |lowerPotential who time history| ≤ potentialBound
  upper_potential_abs :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        |upperPotential who time history| ≤ potentialBound
  deviation_potential_abs :
    ∀ who (deviation : G.BehaviorStrategy who) time,
      time < fuel →
        ∀ history ∈
            (G.histDist
              (Function.update profile who deviation)
              initial time).support,
          |deviationPotential who time history| ≤ potentialBound
  lower_drift :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        lowerPotential who time history ≤
          G.historyContinuationEU profile
            (lowerPotential who) history
  upper_drift :
    ∀ who time, time < fuel →
      ∀ history ∈ (G.histDist profile initial time).support,
        G.historyContinuationEU profile
            (upperPotential who) history ≤
          upperPotential who time history
  deviation_drift :
    ∀ who (deviation : G.BehaviorStrategy who) time,
      time < fuel →
        ∀ history ∈
            (G.histDist
              (Function.update profile who deviation)
              initial time).support,
          G.historyContinuationEU
              (Function.update profile who deviation)
              (deviationPotential who) history ≤
            deviationPotential who time history

namespace BoundedVariableStoppingPrefixPotentials

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)]
  {profile : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}
  {lowerPotential upperPotential deviationPotential :
    ι → G.HistoryPotential}

/-- Canonical absolute-gap charges turn bounded potentials with local drift
into the support-sensitive pointwise prefix data. -/
def toPointwiseData
    (data :
      G.BoundedVariableStoppingPrefixPotentials
        profile initial fuel
        lowerPotential upperPotential deviationPotential) :
    G.PointwiseVariableStoppingPrefixData
      profile initial fuel
      lowerPotential upperPotential deviationPotential
      (fun who =>
        G.historyPotentialGapCharge profile who
          (lowerPotential who))
      (fun who =>
        G.historyPotentialGapCharge profile who
          (upperPotential who))
      (fun who deviation =>
        G.historyPotentialGapCharge
          (Function.update profile who deviation) who
          (deviationPotential who)) where
  region := data.region
  rank_le_fuel := data.rank_le_fuel
  chargeBound := data.payoffBound + data.potentialBound
  chargeBound_nonneg :=
    add_nonneg data.payoffBound_nonneg data.potentialBound_nonneg
  lower_drift := data.lower_drift
  lower_stage := by
    intro who time _ history _
    unfold historyPotentialGapCharge
    linarith [
      neg_le_abs
        (G.stageEUAt profile history who -
          lowerPotential who time history)
    ]
  upper_drift := data.upper_drift
  upper_stage := by
    intro who time _ history _
    unfold historyPotentialGapCharge
    linarith [
      le_abs_self
        (G.stageEUAt profile history who -
          upperPotential who time history)
    ]
  deviation_drift := data.deviation_drift
  deviation_stage := by
    intro who deviation time _ history _
    unfold historyPotentialGapCharge
    linarith [
      le_abs_self
        (G.stageEUAt
            (Function.update profile who deviation) history who -
          deviationPotential who time history)
    ]
  lower_charge_le := by
    intro who time htime history hhistory
    unfold historyPotentialGapCharge
    calc
      |G.stageEUAt profile history who -
          lowerPotential who time history| ≤
        |G.stageEUAt profile history who| +
          |lowerPotential who time history| :=
        abs_sub _ _
      _ ≤ data.payoffBound + data.potentialBound :=
        add_le_add
          (G.abs_stageEUAt_le_of_abs_payoff_le
            profile data.payoff_abs history who)
          (data.lower_potential_abs
            who time htime history hhistory)
  upper_charge_le := by
    intro who time htime history hhistory
    unfold historyPotentialGapCharge
    calc
      |G.stageEUAt profile history who -
          upperPotential who time history| ≤
        |G.stageEUAt profile history who| +
          |upperPotential who time history| :=
        abs_sub _ _
      _ ≤ data.payoffBound + data.potentialBound :=
        add_le_add
          (G.abs_stageEUAt_le_of_abs_payoff_le
            profile data.payoff_abs history who)
          (data.upper_potential_abs
            who time htime history hhistory)
  deviation_charge_le := by
    intro who deviation time htime history hhistory
    unfold historyPotentialGapCharge
    calc
      |G.stageEUAt
          (Function.update profile who deviation) history who -
          deviationPotential who time history| ≤
        |G.stageEUAt
          (Function.update profile who deviation) history who| +
          |deviationPotential who time history| :=
        abs_sub _ _
      _ ≤ data.payoffBound + data.potentialBound :=
        add_le_add
          (G.abs_stageEUAt_le_of_abs_payoff_le
            (Function.update profile who deviation)
            data.payoff_abs history who)
          (data.deviation_potential_abs
            who deviation time htime history hhistory)

/-- The bounded-gap compiler's final expectation-level prefix law.

The exact prefix cost is
`fuel * (payoffBound + potentialBound)`. -/
def toVariableStoppingPrefixLaw
    (data :
      G.BoundedVariableStoppingPrefixPotentials
        profile initial fuel
        lowerPotential upperPotential deviationPotential)
    (error : ℝ) (herror : 0 < error) :
    G.VariableStoppingPrefixLaw profile initial fuel
      lowerPotential upperPotential deviationPotential
      (fun who =>
        G.expectedHistoryCharge profile initial
          (G.historyPotentialGapCharge profile who
            (lowerPotential who)))
      (fun who =>
        G.expectedHistoryCharge profile initial
          (G.historyPotentialGapCharge profile who
            (upperPotential who)))
      (fun who deviation =>
        G.expectedHistoryCharge
          (Function.update profile who deviation) initial
          (G.historyPotentialGapCharge
            (Function.update profile who deviation) who
            (deviationPotential who)))
      error :=
  data.toPointwiseData.toVariableStoppingPrefixLaw error herror

end BoundedVariableStoppingPrefixPotentials

namespace FiniteChildAdaptivePotentialFamily

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] {Child : Type} [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {childError suffixError : ℝ}

/-- The stopped-child suffix producer, specialized so its potential is the
same immediate online-switch potential consumed by the prefix compiler.

The repaired online-rule API connects the post-fuel root decomposition and
online view directly, so no separate compatibility premise remains. -/
def variableStoppingSuffixCaps_onlineSwitch
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    {fuel : ℕ}
    (rule : G.OnlineCausalBoundedStoppingRule fuel)
    (selection : G.BehaviorProfile) (initial : G.State)
    (observe : G.BoundedStoppedHistory fuel → Child)
    (hentry : ∀ base : G.BoundedStoppedHistory fuel,
      base.2.2 = entry (observe base))
    (selectingLower selectingUpper selectingDeviation :
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
        G.onlineSwitchHistoryPotential rule
          (selectingLower who)
          (family.stoppedLowerPotential observe who))
      (fun who =>
        G.onlineSwitchHistoryPotential rule
          (selectingUpper who)
          (family.stoppedUpperPotential observe who))
      (fun who =>
        G.onlineSwitchHistoryPotential rule
          (selectingDeviation who)
          (family.stoppedDeviationPotential observe who))
      (fun who rootTime =>
        G.stoppedChildScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector
          (family.stoppedLowerCharge observe)
          who rootTime)
      (fun who rootTime =>
        G.stoppedChildScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector
          (family.stoppedUpperCharge observe)
          who rootTime)
      (fun who deviation rootTime =>
        G.stoppedChildDeviationScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector
          (family.stoppedDeviationCharge observe)
          who deviation rootTime)
      suffixError := by
  simpa only [
    G.prefixThenStoppedChild_onlineSwitch_eq
      rule
  ] using
    family.variableStoppingSuffixCaps
      rule selection initial observe hentry
      (fun who =>
        G.onlineSwitchHistoryPotential rule
          (selectingLower who)
          (family.stoppedLowerPotential observe who))
      (fun who =>
        G.onlineSwitchHistoryPotential rule
          (selectingUpper who)
          (family.stoppedUpperPotential observe who))
      (fun who =>
        G.onlineSwitchHistoryPotential rule
          (selectingDeviation who)
          (family.stoppedDeviationPotential observe who))
      tail

/-- Ordinary finite child systems automatically produce the immediate-switch
suffix caps at their original error plus any positive slack.

The charge lower bound and signed-tail argument are supplied by
`FiniteAdaptiveChildChargeLowerBound`; no separate tail certificate remains
as an application input. -/
def variableStoppingSuffixCaps_onlineSwitch_of_slack
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    {fuel : ℕ}
    (rule : G.OnlineCausalBoundedStoppingRule fuel)
    (selection : G.BehaviorProfile) (initial : G.State)
    (observe : G.BoundedStoppedHistory fuel → Child)
    (hentry : ∀ base : G.BoundedStoppedHistory fuel,
      base.2.2 = entry (observe base))
    (selectingLower selectingUpper selectingDeviation :
      ι → G.HistoryPotential)
    (slack : ℝ) (slack_pos : 0 < slack) :
    G.VariableStoppingSuffixCaps
      (G.causalTerminalChildDispatcher rule selection
        (family.observedStoppedProfile observe))
      initial fuel
      (fun who =>
        G.onlineSwitchHistoryPotential rule
          (selectingLower who)
          (family.stoppedLowerPotential observe who))
      (fun who =>
        G.onlineSwitchHistoryPotential rule
          (selectingUpper who)
          (family.stoppedUpperPotential observe who))
      (fun who =>
        G.onlineSwitchHistoryPotential rule
          (selectingDeviation who)
          (family.stoppedDeviationPotential observe who))
      (fun who rootTime =>
        G.stoppedChildScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector
          (family.stoppedLowerCharge observe)
          who rootTime)
      (fun who rootTime =>
        G.stoppedChildScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector
          (family.stoppedUpperCharge observe)
          who rootTime)
      (fun who deviation rootTime =>
        G.stoppedChildDeviationScalarCharge
          (G.causalTerminalChildDispatcher rule selection
            (family.observedStoppedProfile observe))
          initial rule.selector
          (family.stoppedDeviationCharge observe)
          who deviation rootTime)
      (childError + slack) :=
  family.variableStoppingSuffixCaps_onlineSwitch
    rule selection initial observe hentry
    selectingLower selectingUpper selectingDeviation
    (family.commonRootChildChargeTailBound
      (G.causalTerminalChildDispatcher rule selection
        (family.observedStoppedProfile observe))
      initial rule.selector observe slack slack_pos)

end FiniteChildAdaptivePotentialFamily

/-- Consume a bounded local prefix and suffix caps stated for the same
immediate online-switch potentials.

This is the connectivity capstone: the output is an ordinary adaptive
potential system, so the immediate-switch prefix producer is not merely a
parallel unused interface. -/
def adaptivePotentialSystemAt_of_onlineVariableStopping
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)]
    {profile : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}
    {target : Payoff ι}
    {lowerPotential upperPotential deviationPotential :
      ι → G.HistoryPotential}
    {suffixLowerCharge suffixUpperCharge : ι → ℕ → ℝ}
    {suffixDeviationCharge :
      ∀ who, G.BehaviorStrategy who → ℕ → ℝ}
    {prefixError suffixError : ℝ}
    (prefixData :
      G.BoundedVariableStoppingPrefixPotentials
        profile initial fuel
        lowerPotential upperPotential deviationPotential)
    (prefixError_pos : 0 < prefixError)
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
      (prefixError + suffixError) :=
  G.adaptivePotentialSystemAt_of_variableStopping
    (prefixData.toVariableStoppingPrefixLaw
      prefixError prefixError_pos)
    suffixCaps lowerInitial upperInitial deviationInitial

end StochasticGame
end GameTheory
