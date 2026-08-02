/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.OccupationFlowAlternative

/-!
# Exact finite discounted-flow accounting

This file isolates the finite algebra behind discounted occupation flows.
An aggregate flow has a stock at each state, a reset source, and a directed
flux.  Its two defining equations are state balance and the fact that a
fraction `1 - reset` of every stock leaves its source.  Summing those equations
over a set of states gives the exact cut identity.

The labelled version records a finite family of stochastic transition rows at
each source.  It supplies the fixed-kernel successor identities and compiles
to the aggregate flow.  No positivity, asymptotic, or strategic hypothesis is
needed for these identities.
-/

open Finset BigOperators

namespace Math
namespace Probability

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Total weight carried by a finite set. -/
def finiteMassOn (weight : S → ℝ) (states : Finset S) : ℝ :=
  ∑ state ∈ states, weight state

/-- Total directed flux from one finite set to another. -/
def finiteFlowBetween (flux : S → S → ℝ)
    (source target : Finset S) : ℝ :=
  ∑ state ∈ source, ∑ next ∈ target, flux state next

/-- Exact aggregate accounting data for a finite discounted flow. -/
structure FiniteDiscountedFlow where
  reset : ℝ
  initial : PMF S
  stock : S → ℝ
  flux : S → S → ℝ
  state_balance : ∀ target,
    stock target = reset * (initial target).toReal + ∑ source, flux source target
  source_balance : ∀ source,
    ∑ target, flux source target = (1 - reset) * stock source

namespace FiniteDiscountedFlow

variable (flow : FiniteDiscountedFlow (S := S))

/-- Stock carried by a finite state set. -/
def stockOn (states : Finset S) : ℝ :=
  finiteMassOn flow.stock states

/-- Initial reset mass carried by a finite state set. -/
def initialOn (states : Finset S) : ℝ :=
  finiteMassOn (fun state => (flow.initial state).toReal) states

/-- Aggregate directed flux between two finite state sets. -/
def between (source target : Finset S) : ℝ :=
  finiteFlowBetween flow.flux source target

theorem between_source_compl (states : Finset S) :
    flow.between states Finset.univ =
      flow.between states states + flow.between states statesᶜ := by
  classical
  unfold between finiteFlowBetween
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source hsource
  rw [Finset.sum_add_sum_compl]

theorem between_target_compl (states : Finset S) :
    flow.between Finset.univ states =
      flow.between states states + flow.between statesᶜ states := by
  classical
  unfold between finiteFlowBetween
  rw [Finset.sum_add_sum_compl]

theorem between_source_univ (states : Finset S) :
    flow.between states Finset.univ =
      (1 - flow.reset) * flow.stockOn states := by
  classical
  unfold between finiteFlowBetween stockOn finiteMassOn
  calc
    (∑ source ∈ states, ∑ target ∈ Finset.univ, flow.flux source target) =
        ∑ source ∈ states, (1 - flow.reset) * flow.stock source := by
          apply Finset.sum_congr rfl
          intro source hsource
          simpa using flow.source_balance source
    _ = (1 - flow.reset) * ∑ source ∈ states, flow.stock source := by
          rw [Finset.mul_sum]

theorem stockOn_state_balance (states : Finset S) :
    flow.stockOn states =
      flow.reset * flow.initialOn states + flow.between Finset.univ states := by
  classical
  unfold stockOn initialOn between finiteMassOn finiteFlowBetween
  calc
    (∑ target ∈ states, flow.stock target) =
        ∑ target ∈ states,
          (flow.reset * (flow.initial target).toReal +
            ∑ source, flow.flux source target) := by
          apply Finset.sum_congr rfl
          intro target htarget
          rw [flow.state_balance target]
    _ = flow.reset * (∑ target ∈ states, (flow.initial target).toReal) +
          ∑ target ∈ states, ∑ source, flow.flux source target := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = flow.reset * (∑ target ∈ states, (flow.initial target).toReal) +
          ∑ source ∈ Finset.univ, ∑ target ∈ states, flow.flux source target := by
          congr 1
          rw [Finset.sum_comm]

/-- Exact discounted cut balance.  Internal flux cancels before any limiting
or residual operation is performed. -/
theorem cut_balance (states : Finset S) :
    flow.reset * flow.stockOn states + flow.between states statesᶜ =
      flow.reset * flow.initialOn states + flow.between statesᶜ states := by
  have hstock := flow.stockOn_state_balance states
  rw [flow.between_target_compl states] at hstock
  have hout := flow.between_source_univ states
  rw [flow.between_source_compl states] at hout
  linarith

end FiniteDiscountedFlow

variable {Label : S → Type*} [∀ state, Fintype (Label state)]

/-- A finite discounted flow whose outgoing mass is split among labelled
stochastic transition rows. -/
structure FiniteDiscountedLabelledFlow where
  reset : ℝ
  initial : PMF S
  stock : S → ℝ
  labelMass : ∀ state, Label state → ℝ
  kernel : ∀ state, Label state → PMF S
  label_mass_sum : ∀ state, ∑ label, labelMass state label = stock state
  state_balance : ∀ target,
    stock target = reset * (initial target).toReal +
      (1 - reset) *
        ∑ state, ∑ label,
          labelMass state label * (kernel state label target).toReal

namespace FiniteDiscountedLabelledFlow

variable (flow : FiniteDiscountedLabelledFlow (S := S) (Label := Label))

/-- Flux carried by one labelled stochastic transition to one successor. -/
def edgeFlux (source : S) (label : Label source) (target : S) : ℝ :=
  (1 - flow.reset) * flow.labelMass source label *
    (flow.kernel source label target).toReal

/-- Flux aggregated over all labels leaving a fixed source. -/
def aggregateFlux (source target : S) : ℝ :=
  ∑ label, flow.edgeFlux source label target

/-- Successors of one fixed labelled transition retain the proportions of its
stochastic kernel. -/
theorem kernel_mul_edgeFlux (source : S) (label : Label source)
    (first second : S) :
    (flow.kernel source label first).toReal *
        flow.edgeFlux source label second =
      (flow.kernel source label second).toReal *
        flow.edgeFlux source label first := by
  simp only [edgeFlux]
  ring

/-- The successor bundle of one label has total mass
`(1 - reset) * labelMass`. -/
theorem sum_edgeFlux (source : S) (label : Label source) :
    ∑ target, flow.edgeFlux source label target =
      (1 - flow.reset) * flow.labelMass source label := by
  classical
  unfold edgeFlux
  calc
    (∑ target,
        (1 - flow.reset) * flow.labelMass source label *
          (flow.kernel source label target).toReal) =
        ((1 - flow.reset) * flow.labelMass source label) *
          ∑ target, (flow.kernel source label target).toReal := by
            rw [Finset.mul_sum]
    _ = (1 - flow.reset) * flow.labelMass source label := by
          rw [pmf_toReal_sum_one, mul_one]

/-- Labelled state balance rewritten directly in terms of edge flux. -/
theorem state_balance_edgeFlux (target : S) :
    flow.stock target = flow.reset * (flow.initial target).toReal +
      ∑ source, ∑ label, flow.edgeFlux source label target := by
  rw [flow.state_balance target]
  unfold edgeFlux
  rw [Finset.mul_sum]
  apply congrArg (fun value => flow.reset * (flow.initial target).toReal + value)
  apply Finset.sum_congr rfl
  intro source hsource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label hlabel
  ring

/-- Forget labels while retaining their aggregate source-to-target flux. -/
def toFiniteDiscountedFlow : FiniteDiscountedFlow (S := S) where
  reset := flow.reset
  initial := flow.initial
  stock := flow.stock
  flux := flow.aggregateFlux
  state_balance := by
    intro target
    simpa [aggregateFlux] using flow.state_balance_edgeFlux target
  source_balance := by
    intro source
    unfold aggregateFlux
    rw [Finset.sum_comm]
    calc
      (∑ label, ∑ target, flow.edgeFlux source label target) =
          ∑ label, (1 - flow.reset) * flow.labelMass source label := by
            apply Finset.sum_congr rfl
            intro label hlabel
            rw [flow.sum_edgeFlux source label]
      _ = (1 - flow.reset) * ∑ label, flow.labelMass source label := by
            rw [Finset.mul_sum]
      _ = (1 - flow.reset) * flow.stock source := by
            rw [flow.label_mass_sum source]

/-- Labelled form of exact discounted cut balance. -/
theorem cut_balance (states : Finset S) :
    flow.reset * finiteMassOn flow.stock states +
        finiteFlowBetween flow.aggregateFlux states statesᶜ =
      flow.reset *
          finiteMassOn (fun state => (flow.initial state).toReal) states +
        finiteFlowBetween flow.aggregateFlux statesᶜ states := by
  exact flow.toFiniteDiscountedFlow.cut_balance states

end FiniteDiscountedLabelledFlow

end

end Probability
end Math
