/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.FixedDepthAdaptiveCertificate
import UniformEquilibrium.Certificates.Public.RandomStoppedSignedChargeTail

/-!
# Automatic lower bounds for finite adaptive-child charges

An ordinary adaptive-potential certificate permits signed scalar charges.
For a finite stochastic game, however, its process inequalities already
force every charge to have a uniform lower bound.

For a lower potential, expected submartingale monotonicity keeps its
expectation above its initial value.  For upper and deviation potentials,
expected supermartingale monotonicity keeps their expectations below their
initial values.  The stage inequalities and the finite stage-payoff bound
then bound all three scalar charges below by the negative of

`finiteStagePayoffBound + terminalPotentialBound`.

Consequently, a finite family of ordinary child adaptive systems satisfies
the signed stopped-tail interface at its original error plus any prescribed
positive slack.  No positivity normalization or additional charge
hypothesis is needed.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι Child : Type} {G : StochasticGame ι}

namespace AdaptivePotentialSystemAt

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)]
  {profile : G.BehaviorProfile} {initial : G.State}
  {target : Payoff ι} {error : ℝ}

/-- An adaptive system remains valid when its error allowance is enlarged.
All operational data, potentials, and scalar charges are unchanged. -/
def increaseError
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    {largerError : ℝ} (error_le : error ≤ largerError) :
    G.AdaptivePotentialSystemAt
      profile initial target largerError where
  horizon := system.horizon
  lowerPotential := system.lowerPotential
  upperPotential := system.upperPotential
  deviationPotential := system.deviationPotential
  lowerCharge := system.lowerCharge
  upperCharge := system.upperCharge
  deviationCharge := system.deviationCharge
  horizon_ge_two := system.horizon_ge_two
  lower_initial := fun who => (system.lower_initial who).trans error_le
  upper_initial := fun who => (system.upper_initial who).trans error_le
  deviation_initial :=
    fun who => (system.deviation_initial who).trans error_le
  lower_submartingale := system.lower_submartingale
  lower_stage := system.lower_stage
  upper_supermartingale := system.upper_supermartingale
  upper_stage := system.upper_stage
  deviation_supermartingale := system.deviation_supermartingale
  deviation_stage := system.deviation_stage
  lower_charge_cesaro := by
    intro who total htotal
    exact (system.lower_charge_cesaro who total htotal).trans error_le
  upper_charge_cesaro := by
    intro who total htotal
    exact (system.upper_charge_cesaro who total htotal).trans error_le
  deviation_charge_cesaro := by
    intro who deviation total htotal
    exact
      (system.deviation_charge_cesaro
        who deviation total htotal).trans error_le

/-- Expected lower potentials stay above their initial value. -/
theorem lower_initialExpectation_le
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (who : ι) (time : ℕ) :
    system.lowerPotential who 0 (G.emptyHist initial) ≤
      G.expectedHistoryValue profile initial
        (system.lowerPotential who) time := by
  calc
    system.lowerPotential who 0 (G.emptyHist initial) =
        G.expectedHistoryValue profile initial
          (system.lowerPotential who) 0 :=
      (G.expectedHistoryValue_zero
        profile initial (system.lowerPotential who)).symm
    _ ≤
        G.expectedHistoryValue profile initial
          (system.lowerPotential who) time := by
      induction time with
      | zero =>
          exact le_rfl
      | succ time ih =>
          exact ih.trans (system.lower_submartingale who time)

/-- Expected upper potentials stay below their initial value. -/
theorem upper_le_initialExpectation
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (who : ι) (time : ℕ) :
    G.expectedHistoryValue profile initial
        (system.upperPotential who) time ≤
      system.upperPotential who 0 (G.emptyHist initial) := by
  calc
    G.expectedHistoryValue profile initial
        (system.upperPotential who) time ≤
      G.expectedHistoryValue profile initial
        (system.upperPotential who) 0 := by
      induction time with
      | zero =>
          exact le_rfl
      | succ time ih =>
          exact (system.upper_supermartingale who time).trans ih
    _ = system.upperPotential who 0 (G.emptyHist initial) :=
      G.expectedHistoryValue_zero
        profile initial (system.upperPotential who)

/-- Every unilateral-deviation potential stays below its initial value
under the corresponding updated law. -/
theorem deviation_le_initialExpectation
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (who : ι) (deviation : G.BehaviorStrategy who) (time : ℕ) :
    G.expectedHistoryValue
        (Function.update profile who deviation) initial
        (system.deviationPotential who) time ≤
      system.deviationPotential who 0 (G.emptyHist initial) := by
  calc
    G.expectedHistoryValue
        (Function.update profile who deviation) initial
        (system.deviationPotential who) time ≤
      G.expectedHistoryValue
        (Function.update profile who deviation) initial
        (system.deviationPotential who) 0 := by
      induction time with
      | zero =>
          exact le_rfl
      | succ time ih =>
          exact
            (system.deviation_supermartingale who deviation time).trans ih
    _ = system.deviationPotential who 0 (G.emptyHist initial) :=
      G.expectedHistoryValue_zero
        (Function.update profile who deviation) initial
        (system.deviationPotential who)

/-- A payoff bound and a bound on the initial lower potential force a
uniform lower bound on the lower scalar charge. -/
theorem neg_add_le_lowerCharge
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (who : ι)
    {payoffBound potentialBound : ℝ}
    (payoff_bound :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (initial_bound :
      |system.lowerPotential who 0 (G.emptyHist initial)| ≤
        potentialBound)
    (time : ℕ) :
    -(payoffBound + potentialBound) ≤
      system.lowerCharge who time := by
  have stage_abs :
      |G.expectedStagePayoff profile initial time who| ≤
        payoffBound :=
    G.abs_expectedStagePayoff_le
      (fun state action => payoff_bound state action who)
      profile initial time
  have initial_floor :
      -potentialBound ≤
        system.lowerPotential who 0 (G.emptyHist initial) :=
    (abs_le.mp initial_bound).1
  have potential_floor :=
    initial_floor.trans (system.lower_initialExpectation_le who time)
  have stage_upper :
      G.expectedStagePayoff profile initial time who ≤ payoffBound :=
    (abs_le.mp stage_abs).2
  linarith [system.lower_stage who time]

/-- A payoff bound and a bound on the initial upper potential force a
uniform lower bound on the upper scalar charge. -/
theorem neg_add_le_upperCharge
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (who : ι)
    {payoffBound potentialBound : ℝ}
    (payoff_bound :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (initial_bound :
      |system.upperPotential who 0 (G.emptyHist initial)| ≤
        potentialBound)
    (time : ℕ) :
    -(payoffBound + potentialBound) ≤
      system.upperCharge who time := by
  have stage_abs :
      |G.expectedStagePayoff profile initial time who| ≤
        payoffBound :=
    G.abs_expectedStagePayoff_le
      (fun state action => payoff_bound state action who)
      profile initial time
  have initial_ceiling :
      system.upperPotential who 0 (G.emptyHist initial) ≤
        potentialBound :=
    (abs_le.mp initial_bound).2
  have potential_ceiling :=
    (system.upper_le_initialExpectation who time).trans initial_ceiling
  have stage_lower :
      -payoffBound ≤
        G.expectedStagePayoff profile initial time who :=
    (abs_le.mp stage_abs).1
  linarith [system.upper_stage who time]

/-- The same automatic lower bound holds for the scalar charge under every
unilateral updated law. -/
theorem neg_add_le_deviationCharge
    (system :
      G.AdaptivePotentialSystemAt profile initial target error)
    (who : ι)
    {payoffBound potentialBound : ℝ}
    (payoff_bound :
      ∀ state action player,
        |G.stagePayoff state action player| ≤ payoffBound)
    (initial_bound :
      |system.deviationPotential who 0 (G.emptyHist initial)| ≤
        potentialBound)
    (deviation : G.BehaviorStrategy who) (time : ℕ) :
    -(payoffBound + potentialBound) ≤
      system.deviationCharge who deviation time := by
  let updated := Function.update profile who deviation
  have stage_abs :
      |G.expectedStagePayoff updated initial time who| ≤
        payoffBound :=
    G.abs_expectedStagePayoff_le
      (fun state action => payoff_bound state action who)
      updated initial time
  have initial_ceiling :
      system.deviationPotential who 0 (G.emptyHist initial) ≤
        potentialBound :=
    (abs_le.mp initial_bound).2
  have potential_ceiling :=
    (system.deviation_le_initialExpectation who deviation time).trans
      initial_ceiling
  have stage_lower :
      -payoffBound ≤
        G.expectedStagePayoff updated initial time who :=
    (abs_le.mp stage_abs).1
  linarith [system.deviation_stage who deviation time]

end AdaptivePotentialSystemAt

namespace FiniteChildAdaptivePotentialFamily

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {childError : ℝ}

/-- Enlarge every child's error allowance without changing any profile,
potential, charge, or horizon. -/
def increaseError
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    {largerError : ℝ} (error_le : childError ≤ largerError) :
    G.FiniteChildAdaptivePotentialFamily entry target largerError where
  profile := family.profile
  system := fun child => (family.system child).increaseError error_le
  commonHorizon := family.commonHorizon
  commonHorizon_ge_two := family.commonHorizon_ge_two
  horizon_le_common := family.horizon_le_common

/-- The canonical common lower-bound magnitude for all scalar charges in a
finite adaptive-child family. -/
def scalarChargeLowerBound
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError) :
    ℝ :=
  G.finiteStagePayoffBound + family.terminalPotentialBound

theorem scalarChargeLowerBound_nonneg
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError) :
    0 ≤ family.scalarChargeLowerBound :=
  add_nonneg G.finiteStagePayoffBound_nonneg
    family.terminalPotentialBound_nonneg

/-- The original, unmodified child charges are uniformly bounded below.
This is the exact input needed by signed stopped-tail accounting. -/
theorem childScalarChargesBoundedBelow
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    {fuel : ℕ}
    (observe : G.BoundedStoppedHistory fuel → Child) :
    G.ChildScalarChargesBoundedBelow
      (family.stoppedLowerCharge observe)
      (family.stoppedUpperCharge observe)
      (family.stoppedDeviationCharge observe)
      family.scalarChargeLowerBound where
  bound_nonneg := family.scalarChargeLowerBound_nonneg
  lower := by
    intro base who time
    exact
      (family.system (observe base)).neg_add_le_lowerCharge
        who
        (fun state action player =>
          G.abs_stagePayoff_le_finiteStagePayoffBound
            state action player)
        (family.abs_lowerTerminalTarget_le_terminalPotentialBound
          (observe base) who)
        time
  upper := by
    intro base who time
    exact
      (family.system (observe base)).neg_add_le_upperCharge
        who
        (fun state action player =>
          G.abs_stagePayoff_le_finiteStagePayoffBound
            state action player)
        (family.abs_upperTerminalTarget_le_terminalPotentialBound
          (observe base) who)
        time
  deviation := by
    intro base who strategy time
    exact
      (family.system (observe base)).neg_add_le_deviationCharge
        who
        (fun state action player =>
          G.abs_stagePayoff_le_finiteStagePayoffBound
            state action player)
        (family.abs_deviationTerminalTarget_le_terminalPotentialBound
          (observe base) who)
        strategy time

/-- Ordinary finite child adaptive systems automatically acquire the
common-root shifted-tail bound after bounded stopping, at arbitrarily small
additional positive error. -/
def commonRootChildChargeTailBound
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target childError)
    {fuel : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (observe : G.BoundedStoppedHistory fuel → Child)
    (slack : ℝ) (slack_pos : 0 < slack) :
    G.CommonRootChildChargeTailBound
      profile initial selector
      (family.stoppedLowerCharge observe)
      (family.stoppedUpperCharge observe)
      (family.stoppedDeviationCharge observe)
      (childError + slack) :=
  family.commonRootChildChargeTailBound_of_boundedBelow
    profile initial selector observe family.scalarChargeLowerBound
    (family.childScalarChargesBoundedBelow observe)
    slack slack_pos

end FiniteChildAdaptivePotentialFamily
end StochasticGame
end GameTheory
