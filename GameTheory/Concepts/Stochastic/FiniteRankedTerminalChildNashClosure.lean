/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.DelayedFullHorizonChildEnvelope
import GameTheory.Concepts.Stochastic.FiniteHorizonProfileLawTransfer
import GameTheory.Concepts.Stochastic.FinitePublicTerminalNashSystem

/-!
# Finite ranked terminal-child Nash closure

**Partial prototype.**  This is *not* a closure certificate for a
well-founded public child recursion.  It only covers a fixed common terminal
depth, and its root estimates are conditional on the `ObstacleCloseness`
hypothesis, which is assumed rather than derived here.  Genuine early
stopping requires a stopped-tree Nash transfer theorem, which is not yet
available.

What is actually established.  Assume that every terminal public history at
the common depth `fuel` is assigned a legal child with the same entry state,
and that every child has strictly lower rank.  Then:

* the delayed child dispatcher agrees with the backward-induction profile at
  every stage strictly before `fuel`
  (`dispatcher_profilesAgreeBefore`);
* under `ObstacleCloseness`, the delayed lower, upper, and prescribed
  deviation roots each sit within one child error of the endogenous parent
  target (`lower_root_close_parentTarget`, `upper_root_close_parentTarget`,
  `prescribedDeviationRoot_close_parentTarget`).

The output payoff is endogenous: it is the backward-induction Nash payoff of
the fixed terminal child-target obstacle (`parentTarget`).  No external
parent target is preserved.  The selected profile is independent of the
requested accuracy.

Stopping exactly at the common terminal depth is essential to what is proved
here: it is what makes the delayed dispatcher agree with the
backward-induction profile throughout the terminal-payoff game.  No error
budget is allocated in this file, and no incentive-safety statement for the
composed object is claimed.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability
open Math.ProbabilityMassFunction

variable {ι Child : Type} {G : StochasticGame ι}

/-- Total legal child coverage at a fixed public terminal depth, together
with the strict rank decrease needed by the surrounding recursion.

The rule is required to reveal no child before `fuel` on any public history,
and its completed selector must choose the endpoint.  These are pathwise
requirements, hence include histories reachable only after deviations. -/
structure FiniteRankedTerminalChildCoverage
    [Fintype Child]
    (entry : Child → G.State) (fuel : ℕ) where
  rule : G.OnlineCausalBoundedStoppingRule fuel
  initial : G.State
  observe : G.BoundedStoppedHistory fuel → Child
  entry_eq : ∀ base, base.2.2 = entry (observe base)
  parentRank : ℕ
  childRank : Child → ℕ
  childRank_lt : ∀ child, childRank child < parentRank
  view_eq_none_of_lt :
    ∀ time (history : G.Hist time), time < fuel →
      rule.view time history = none
  selector_eq_last :
    ∀ history : G.Hist fuel,
      rule.selector history = Fin.last fuel

namespace FiniteRankedTerminalChildCoverage

variable
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    [Fintype Child]
    {entry : Child → G.State} {childTarget : Child → Payoff ι}
    {fuel : ℕ}
    (coverage :
      G.FiniteRankedTerminalChildCoverage entry fuel)

/-- The public child selected at a complete terminal history. -/
def terminalChild (history : G.Hist fuel) : Child :=
  coverage.observe
    (⟨Fin.last fuel, history⟩ :
      G.BoundedStoppedHistory fuel)

/-- Fixed terminal child-target obstacle.  It does not depend on the
accuracy or on the chosen child potential witnesses. -/
def targetObstacle
    (childTarget : Child → Payoff ι) :
    G.Hist fuel → Payoff ι :=
  fun history => childTarget (coverage.terminalChild history)

/-- Backward-induction public profile for the fixed child-target obstacle. -/
def selection (childTarget : Child → Payoff ι) :
    G.BehaviorProfile :=
  FinitePublicTerminalNashSystem.profile
    (G := G) (coverage.targetObstacle childTarget)

/-- The endogenous parent payoff.  This is fixed before any requested
accuracy is chosen. -/
def parentTarget (childTarget : Child → Payoff ι) :
    Payoff ι :=
  FinitePublicTerminalNashSystem.rootPayoff
    (G := G) (coverage.targetObstacle childTarget)
    coverage.initial

/-- The endogenous parent payoff is exactly the terminal child-target
expectation under the backward-induction selection. -/
theorem parentTarget_eq_expect
    (childTarget : Child → Payoff ι) (who : ι) :
    coverage.parentTarget childTarget who =
      expect
        (G.histDist (coverage.selection childTarget)
          coverage.initial fuel)
        (fun history =>
          coverage.targetObstacle childTarget history who) := by
  symm
  exact
    FinitePublicTerminalNashSystem.expect_obstacle_profile_eq_root
      (coverage.targetObstacle childTarget) coverage.initial who

/-- A vacuous all-terminal region supplies the bookkeeping field required
by the existing delayed prefix compiler. -/
def allTerminalRegion : G.FinitePublicCoinStoppingRegion where
  terminal := fun _ => True
  kernel := fun state => PMF.pure state
  rank := fun _ => 0
  terminal_of_rank_zero := fun _ _ => trivial
  transition_eq_kernel := by
    intro state not_terminal
    exact False.elim (not_terminal trivial)
  step_rank := by
    intro state _ not_terminal
    exact False.elim (not_terminal trivial)

/-- Concrete delayed-envelope data obtained from one chosen finite family of
child witnesses. -/
def delayedData
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily
        entry childTarget childError) :
    G.DelayedFullHorizonChildEnvelopeData
      entry childTarget childError fuel where
  family := family
  rule := coverage.rule
  selection := coverage.selection childTarget
  initial := coverage.initial
  observe := coverage.observe
  entry_eq := coverage.entry_eq
  region := allTerminalRegion (G := G)
  rank_le_fuel := Nat.zero_le fuel

/-- The delayed dispatcher agrees with the backward-induction selection at
every stage relevant to the terminal-payoff game. -/
theorem dispatcher_eq_selection_of_lt
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily
        entry childTarget childError)
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    (coverage.delayedData family).dispatcher who time history =
      coverage.selection childTarget who time history := by
  unfold DelayedFullHorizonChildEnvelopeData.dispatcher
  unfold causalTerminalChildDispatcher
  change
    (match coverage.rule.view time history with
      | none => coverage.selection childTarget who time history
      | some path =>
          family.observedStoppedProfile coverage.observe
            path.base who path.suffixLength path.suffix) =
      coverage.selection childTarget who time history
  rw [coverage.view_eq_none_of_lt time history time_lt]

/-- Profile-level form of terminal-horizon agreement. -/
theorem dispatcher_profilesAgreeBefore
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily
        entry childTarget childError) :
    G.ProfilesAgreeBefore
      (coverage.delayedData family).dispatcher
      (coverage.selection childTarget) fuel :=
  fun who time history time_lt =>
    coverage.dispatcher_eq_selection_of_lt
      family who (time := time) history time_lt

/-- Pointwise comparison between the three selected child initial
potentials and the fixed child-target obstacle. -/
structure ObstacleCloseness
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily
        entry childTarget childError) : Prop where
  lower : ∀ history who,
    |(coverage.delayedData family).lowerObstacle history who -
        coverage.targetObstacle childTarget history who| ≤
      childError
  upper : ∀ history who,
    |(coverage.delayedData family).upperObstacle history who -
        coverage.targetObstacle childTarget history who| ≤
      childError
  deviation : ∀ history who,
    |(coverage.delayedData family).deviationObstacle history who -
        coverage.targetObstacle childTarget history who| ≤
      childError

omit [DecidableEq ι] [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] in
private theorem abs_expect_sub_expect_le
    {Ω : Type} [Finite Ω] (law : PMF Ω)
    (left right : Ω → ℝ) {bound : ℝ}
    (close : ∀ point, |left point - right point| ≤ bound) :
    |expect law left - expect law right| ≤ bound := by
  rw [← expect_sub]
  exact abs_expect_le_of_abs_le law _ close

/-- Prescribed full-history root value expressed as a terminal expectation. -/
theorem prescribedRoot_eq_expect
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily
        entry childTarget childError)
    (obstacle : G.Hist fuel → Payoff ι) (who : ι) :
    (G.finiteFullHistoryControlledStoppingModel
      (coverage.delayedData family).dispatcher
      obstacle).prescribedPotential
        who
        (FinitePublicHistoryControlledStoppingModel.root
          (fuel := fuel) coverage.initial) =
      expect
        (G.histDist
          (coverage.delayedData family).dispatcher
          coverage.initial fuel)
        (fun history => obstacle history who) := by
  symm
  exact
    FiniteFullHistoryControlledStoppingModel.expect_obstacle_eq_prescribedPotential
      (coverage.delayedData family).dispatcher
      obstacle coverage.initial who

/-- The actual delayed lower root is within one child error of the
endogenous terminal Nash target. -/
theorem lower_root_close_parentTarget
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily
        entry childTarget childError)
    (close : coverage.ObstacleCloseness family)
    (who : ι) :
    |(coverage.delayedData family).lowerPotential
          who 0 (G.emptyHist coverage.initial) -
        coverage.parentTarget childTarget who| ≤
      childError := by
  let data := coverage.delayedData family
  rw [
    data.lowerPotential_eq_prefix_of_le
      who (G.emptyHist coverage.initial) (Nat.zero_le fuel)
  ]
  change
    |(G.finiteFullHistoryControlledStoppingModel
          data.dispatcher data.lowerObstacle).prescribedPotential
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) coverage.initial) -
        coverage.parentTarget childTarget who| ≤
      childError
  rw [coverage.prescribedRoot_eq_expect family data.lowerObstacle who]
  rw [
    G.expect_terminal_eq_of_profilesAgreeBefore
      (coverage.dispatcher_profilesAgreeBefore family)
      (fun history => data.lowerObstacle history who)
  ]
  rw [coverage.parentTarget_eq_expect childTarget who]
  exact
    abs_expect_sub_expect_le
      (G.histDist (coverage.selection childTarget)
        coverage.initial fuel)
      (fun history => data.lowerObstacle history who)
      (fun history =>
        coverage.targetObstacle childTarget history who)
      (fun history => close.lower history who)

/-- The actual delayed upper root has the same automatic anchor. -/
theorem upper_root_close_parentTarget
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily
        entry childTarget childError)
    (close : coverage.ObstacleCloseness family)
    (who : ι) :
    |(coverage.delayedData family).upperPotential
          who 0 (G.emptyHist coverage.initial) -
        coverage.parentTarget childTarget who| ≤
      childError := by
  let data := coverage.delayedData family
  rw [
    data.upperPotential_eq_prefix_of_le
      who (G.emptyHist coverage.initial) (Nat.zero_le fuel)
  ]
  change
    |(G.finiteFullHistoryControlledStoppingModel
          data.dispatcher data.upperObstacle).prescribedPotential
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) coverage.initial) -
        coverage.parentTarget childTarget who| ≤
      childError
  rw [coverage.prescribedRoot_eq_expect family data.upperObstacle who]
  rw [
    G.expect_terminal_eq_of_profilesAgreeBefore
      (coverage.dispatcher_profilesAgreeBefore family)
      (fun history => data.upperObstacle history who)
  ]
  rw [coverage.parentTarget_eq_expect childTarget who]
  exact
    abs_expect_sub_expect_le
      (G.histDist (coverage.selection childTarget)
        coverage.initial fuel)
      (fun history => data.upperObstacle history who)
      (fun history =>
        coverage.targetObstacle childTarget history who)
      (fun history => close.upper history who)

/-- The prescribed delayed deviation root is automatically anchored at the
same endogenous payoff. -/
theorem prescribedDeviationRoot_close_parentTarget
    {childError : ℝ}
    (family :
      G.FiniteChildAdaptivePotentialFamily
        entry childTarget childError)
    (close : coverage.ObstacleCloseness family)
    (who : ι) :
    |(coverage.delayedData family).prescribedDeviationRoot who -
        coverage.parentTarget childTarget who| ≤
      childError := by
  let data := coverage.delayedData family
  change
    |(G.finiteFullHistoryControlledStoppingModel
          data.dispatcher data.deviationObstacle).prescribedPotential
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) coverage.initial) -
        coverage.parentTarget childTarget who| ≤
      childError
  rw [coverage.prescribedRoot_eq_expect family data.deviationObstacle who]
  rw [
    G.expect_terminal_eq_of_profilesAgreeBefore
      (coverage.dispatcher_profilesAgreeBefore family)
      (fun history => data.deviationObstacle history who)
  ]
  rw [coverage.parentTarget_eq_expect childTarget who]
  exact
    abs_expect_sub_expect_le
      (G.histDist (coverage.selection childTarget)
        coverage.initial fuel)
      (fun history => data.deviationObstacle history who)
      (fun history =>
        coverage.targetObstacle childTarget history who)
      (fun history => close.deviation history who)

end FiniteRankedTerminalChildCoverage

end StochasticGame
end GameTheory
