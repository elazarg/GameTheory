/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.PMFProduct
import Math.Probability.FiniteDiscountedFlow

/-!
# Finite discounted product-flow kinematics

This file packages the exact product-flow equations used by finite stochastic
games without adding payoff or equilibrium data.  State occupation and every
mixed action are represented by PMFs.  The joint-action mass is therefore the
state mass times the independent product of the action marginals.

Balanced product-flow data compile to the labelled discounted-flow API.  The
generic state, cut, and successor-bundle identities can then be reused without
reproving their finite-sum algebra.

This is a kinematic interface only: it contains no converse realization or
strategic-sufficiency assertion.
-/

set_option autoImplicit false

open Finset BigOperators

namespace Math
namespace Probability

noncomputable section

open PMFProduct

universe uS uI uA

variable {S : Type uS} {I : Type uI}
  [Fintype S] [DecidableEq S]
  [Fintype I] [DecidableEq I]
  {Action : S → I → Type uA}
  [∀ state player, Fintype (Action state player)]

/-- Joint action available at one state. -/
abbrev FiniteJointAction (Action : S → I → Type uA) (state : S) :=
  ∀ player, Action state player

/-- The probability and kernel data underlying a finite discounted product
flow.  Balance is imposed separately, after the derived masses are defined. -/
structure FiniteProductFlowData (Action : S → I → Type uA) where
  reset : ℝ
  initial : PMF S
  occupation : PMF S
  profile : ∀ state player, PMF (Action state player)
  kernel : ∀ state, FiniteJointAction Action state → PMF S

namespace FiniteProductFlowData

variable (data : FiniteProductFlowData (S := S) (I := I) Action)

/-- Independent joint-action law at one state. -/
def jointActionLaw (state : S) : PMF (FiniteJointAction Action state) :=
  pmfPi (data.profile state)

/-- Occupation mass carried by one state-labelled joint action. -/
def actionMass (state : S) (action : FiniteJointAction Action state) : ℝ :=
  (data.occupation state).toReal * (data.jointActionLaw state action).toReal

/-- Directed successor flux of one state-labelled joint action. -/
def edgeFlux (state : S) (action : FiniteJointAction Action state)
    (target : S) : ℝ :=
  (1 - data.reset) * data.actionMass state action *
    (data.kernel state action target).toReal

/-- Exact discounted state balance for product-flow data. -/
def IsBalanced : Prop :=
  ∀ target,
    (data.occupation target).toReal =
      data.reset * (data.initial target).toReal +
        (1 - data.reset) *
          ∑ state, ∑ action,
            data.actionMass state action *
              (data.kernel state action target).toReal

@[simp] theorem jointActionLaw_apply (state : S)
    (action : FiniteJointAction Action state) :
    data.jointActionLaw state action =
      ∏ player, data.profile state player (action player) :=
  rfl

/-- Exact Segre-product formula for a labelled action mass. -/
theorem actionMass_eq_product (state : S)
    (action : FiniteJointAction Action state) :
    data.actionMass state action =
      (data.occupation state).toReal *
        ∏ player, (data.profile state player (action player)).toReal := by
  simp [actionMass, jointActionLaw, pmfPi_apply]

theorem actionMass_nonneg (state : S)
    (action : FiniteJointAction Action state) :
    0 ≤ data.actionMass state action :=
  mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- Swapping one coordinate between two joint actions preserves the product
of their independent joint-action probabilities. -/
theorem jointActionLaw_swap_mul (state : S)
    (first second : FiniteJointAction Action state) (player : I) :
    data.jointActionLaw state first * data.jointActionLaw state second =
      data.jointActionLaw state
          (Function.update first player (second player)) *
        data.jointActionLaw state
          (Function.update second player (first player)) := by
  classical
  simp only [jointActionLaw_apply]
  rw [prod_factor_erase (fun who action => data.profile state who action)
      player first,
    prod_factor_erase (fun who action => data.profile state who action)
      player second,
    prod_factor_erase (fun who action => data.profile state who action)
      player (Function.update first player (second player)),
    prod_factor_erase (fun who action => data.profile state who action)
      player (Function.update second player (first player)),
    prod_erase_update_eq
      (fun who action => data.profile state who action) player first,
    prod_erase_update_eq
      (fun who action => data.profile state who action) player second]
  simp only [Function.update_self]
  ring

/-- One-coordinate Segre binomial for the real product-flow masses. -/
theorem actionMass_swap_mul (state : S)
    (first second : FiniteJointAction Action state) (player : I) :
    data.actionMass state first * data.actionMass state second =
      data.actionMass state
          (Function.update first player (second player)) *
        data.actionMass state
          (Function.update second player (first player)) := by
  have hweight := congrArg ENNReal.toReal
    (data.jointActionLaw_swap_mul state first second player)
  simp only [ENNReal.toReal_mul] at hweight
  unfold actionMass
  calc
    ((data.occupation state).toReal *
          (data.jointActionLaw state first).toReal) *
        ((data.occupation state).toReal *
          (data.jointActionLaw state second).toReal) =
      (data.occupation state).toReal ^ 2 *
        ((data.jointActionLaw state first).toReal *
          (data.jointActionLaw state second).toReal) := by ring
    _ = (data.occupation state).toReal ^ 2 *
        ((data.jointActionLaw state
            (Function.update first player (second player))).toReal *
          (data.jointActionLaw state
            (Function.update second player (first player))).toReal) := by
          rw [hweight]
    _ = ((data.occupation state).toReal *
          (data.jointActionLaw state
            (Function.update first player (second player))).toReal) *
        ((data.occupation state).toReal *
          (data.jointActionLaw state
            (Function.update second player (first player))).toReal) := by ring

/-- Product action masses disintegrate exactly to the state occupation mass. -/
theorem sum_actionMass (state : S) :
    ∑ action, data.actionMass state action =
      (data.occupation state).toReal := by
  classical
  unfold actionMass
  calc
    (∑ action,
        (data.occupation state).toReal *
          (data.jointActionLaw state action).toReal) =
        (data.occupation state).toReal *
          ∑ action, (data.jointActionLaw state action).toReal := by
            rw [Finset.mul_sum]
    _ = (data.occupation state).toReal := by
          rw [pmf_toReal_sum_one, mul_one]

/-- The state occupation vector is a simplex point. -/
theorem sum_occupation :
    ∑ state, (data.occupation state).toReal = 1 :=
  pmf_toReal_sum_one data.occupation

/-- Every state/player action vector is a simplex point. -/
theorem sum_profile (state : S) (player : I) :
    ∑ action, (data.profile state player action).toReal = 1 :=
  pmf_toReal_sum_one (data.profile state player)

/-- Fixed-kernel successor proportionality, stated directly for product
flows. -/
theorem kernel_mul_edgeFlux (state : S)
    (action : FiniteJointAction Action state) (first second : S) :
    (data.kernel state action first).toReal *
        data.edgeFlux state action second =
      (data.kernel state action second).toReal *
        data.edgeFlux state action first := by
  simp only [edgeFlux]
  ring

/-- All successors of a fixed state/action label form one stochastic bundle. -/
theorem sum_edgeFlux (state : S)
    (action : FiniteJointAction Action state) :
    ∑ target, data.edgeFlux state action target =
      (1 - data.reset) * data.actionMass state action := by
  classical
  unfold edgeFlux
  calc
    (∑ target,
        (1 - data.reset) * data.actionMass state action *
          (data.kernel state action target).toReal) =
        ((1 - data.reset) * data.actionMass state action) *
          ∑ target, (data.kernel state action target).toReal := by
            rw [Finset.mul_sum]
    _ = (1 - data.reset) * data.actionMass state action := by
          rw [pmf_toReal_sum_one, mul_one]

/-- Compile balanced product-flow data to the generic labelled-flow API. -/
def toFiniteDiscountedLabelledFlow (hbalance : data.IsBalanced) :
    FiniteDiscountedLabelledFlow
      (S := S) (Label := fun state => FiniteJointAction Action state) where
  reset := data.reset
  initial := data.initial
  stock := fun state => (data.occupation state).toReal
  labelMass := data.actionMass
  kernel := data.kernel
  label_mass_sum := data.sum_actionMass
  state_balance := by
    intro target
    exact hbalance target

/-- Aggregate source-to-target flux, retaining the action-labelled flux as a
finite sum. -/
def aggregateFlux (source target : S) : ℝ :=
  ∑ action, data.edgeFlux source action target

/-- Exact state balance in the edge-flux notation. -/
theorem state_balance_edgeFlux (hbalance : data.IsBalanced) (target : S) :
    (data.occupation target).toReal =
      data.reset * (data.initial target).toReal +
        ∑ source, ∑ action, data.edgeFlux source action target := by
  exact (data.toFiniteDiscountedLabelledFlow hbalance).state_balance_edgeFlux target

/-- The aggregate flux leaving a state is the non-reset fraction of its
occupation stock. -/
theorem sum_aggregateFlux (source : S) :
    ∑ target, data.aggregateFlux source target =
      (1 - data.reset) * (data.occupation source).toReal := by
  classical
  unfold aggregateFlux
  rw [Finset.sum_comm]
  calc
    (∑ action, ∑ target, data.edgeFlux source action target) =
        ∑ action, (1 - data.reset) * data.actionMass source action := by
          apply Finset.sum_congr rfl
          intro action haction
          rw [data.sum_edgeFlux source action]
    _ = (1 - data.reset) * ∑ action, data.actionMass source action := by
          rw [Finset.mul_sum]
    _ = (1 - data.reset) * (data.occupation source).toReal := by
          rw [data.sum_actionMass source]

/-- Balanced product data satisfy the exact discounted cut equation. -/
theorem cut_balance (hbalance : data.IsBalanced) (states : Finset S) :
    data.reset *
          finiteMassOn (fun state => (data.occupation state).toReal) states +
        finiteFlowBetween data.aggregateFlux states statesᶜ =
      data.reset *
          finiteMassOn (fun state => (data.initial state).toReal) states +
        finiteFlowBetween data.aggregateFlux statesᶜ states := by
  exact (data.toFiniteDiscountedLabelledFlow hbalance).cut_balance states

end FiniteProductFlowData

/-- Product-flow data together with their exact discounted state equation. -/
structure FiniteDiscountedProductFlow (Action : S → I → Type uA)
    [∀ state player, Fintype (Action state player)] where
  data : FiniteProductFlowData (S := S) (I := I) Action
  balanced : data.IsBalanced

namespace FiniteDiscountedProductFlow

variable (flow : FiniteDiscountedProductFlow (S := S) (I := I) Action)

theorem cut_balance (states : Finset S) :
    flow.data.reset *
          finiteMassOn
            (fun state => (flow.data.occupation state).toReal) states +
        finiteFlowBetween flow.data.aggregateFlux states statesᶜ =
      flow.data.reset *
          finiteMassOn (fun state => (flow.data.initial state).toReal) states +
        finiteFlowBetween flow.data.aggregateFlux statesᶜ states :=
  flow.data.cut_balance flow.balanced states

end FiniteDiscountedProductFlow

end

end Probability
end Math
