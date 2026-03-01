import GameTheory.BayesianGame

/-!
# Mechanism Design Basics

Defines mechanisms and incentive compatibility (IC). A mechanism specifies
an outcome rule given players' reported types. It is incentive-compatible
if truthful reporting is a Bayes-Nash equilibrium.

## Main definitions

* `Mechanism` — a mechanism with outcome rule
* `Mechanism.isIC` — (dominant-strategy) incentive compatibility
* `Mechanism.isBIC` — Bayesian incentive compatibility

## Main results

* `isIC_implies_isBIC` — dominant-strategy IC implies Bayesian IC
-/

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-- A (direct) mechanism: players report types, the mechanism maps
    reported types to payoffs for each player. -/
structure Mechanism (ι : Type) [Fintype ι] where
  /-- Type space for each player. -/
  Θ : ι → Type
  [instFintypeΘ : ∀ i, Fintype (Θ i)]
  [instNonemptyΘ : ∀ i, Nonempty (Θ i)]
  /-- Outcome rule: maps reported types to per-player payoff. -/
  outcome : (∀ i, Θ i) → ι → ℝ

attribute [instance] Mechanism.instFintypeΘ Mechanism.instNonemptyΘ

namespace Mechanism

open Classical in
/-- Dominant-strategy incentive compatibility: for every player, truthful
    reporting is weakly better regardless of others' reports. -/
def isIC (M : Mechanism ι) : Prop :=
  ∀ (who : ι) (θ : ∀ i, M.Θ i) (θ' : M.Θ who),
    M.outcome θ who ≥ M.outcome (Function.update θ who θ') who

open Classical in
/-- Bayesian incentive compatibility given a common prior `μ`:
    for every player and every pair of types, truthfully reporting is
    weakly better in expectation (weighted by prior probability of that type). -/
def isBIC (M : Mechanism ι) (μ : PMF (∀ i, M.Θ i)) : Prop :=
  ∀ (who : ι) (θ' : M.Θ who),
    expect μ (fun θ => M.outcome θ who) ≥
    expect μ (fun θ => M.outcome (Function.update θ who θ') who)

open Classical in
/-- Dominant-strategy IC implies Bayesian IC for any prior. -/
theorem isIC_implies_isBIC (M : Mechanism ι) (hIC : M.isIC) (μ : PMF (∀ i, M.Θ i)) :
    M.isBIC μ := by
  intro who θ'
  simp only [expect_eq_sum, ge_iff_le]
  apply Finset.sum_le_sum
  intro θ _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact hIC who θ θ'

open Classical in
/-- The Bayesian game induced by a mechanism with prior `μ`:
    types = mechanism types, actions = reported types. -/
noncomputable def inducedBayesianGame (M : Mechanism ι)
    (μ : PMF (∀ i, M.Θ i)) : BayesianGame ι where
  Θ := M.Θ
  Act := M.Θ  -- actions are reported types
  prior := μ
  utility := fun _ report who => M.outcome report who

/-- The truthful strategy: each player reports their true type. -/
def truthful (M : Mechanism ι) (μ : PMF (∀ i, M.Θ i)) :
    (M.inducedBayesianGame μ).BProfile :=
  fun _ θ => θ

end Mechanism

end GameTheory
