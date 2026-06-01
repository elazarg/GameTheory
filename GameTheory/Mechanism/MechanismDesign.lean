/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.BayesianGame
import Math.Probability
import Math.ProbabilityMassFunction

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

open Math.Probability

variable {ι : Type}

/-- A (direct) mechanism: players report types, the mechanism maps
    reported types to payoffs for each player. -/
structure Mechanism (ι : Type) where
  /-- Type space for each player. -/
  Θ : ι → Type
  /-- Outcome rule: maps reported types to per-player payoff. -/
  outcome : (∀ i, Θ i) → ι → ℝ

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
theorem isIC_implies_isBIC (M : Mechanism ι) [Finite (∀ i, M.Θ i)]
    (hIC : M.isIC) (μ : PMF (∀ i, M.Θ i)) :
    M.isBIC μ := by
  intro who θ'
  rw [ge_iff_le]
  exact Math.ProbabilityMassFunction.expect_mono_of_pointwise μ
    (fun θ => M.outcome (Function.update θ who θ') who)
    (fun θ => M.outcome θ who)
    (fun θ => hIC who θ θ')

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

open Classical in
/-- Auxiliary: applying an update of the truthful strategy at `who` to a
type profile `θ` is the same as updating `θ` itself at `who` with the
corresponding image. -/
theorem update_truthful_apply (M : Mechanism ι)
    (μ : PMF (∀ i, M.Θ i))
    (who : ι) (s' : M.Θ who → M.Θ who) (θ : ∀ j, M.Θ j) :
    (fun i => Function.update (M.truthful μ) who s' i (θ i)) =
    Function.update θ who (s' (θ who)) := by
  classical
  ext i
  by_cases hi : i = who
  · subst hi; simp [Function.update]
  · simp [truthful, Function.update_of_ne hi]

open Classical in
/-- Dominant-strategy IC implies truthful reporting is a Bayes-Nash
    equilibrium of the induced game (for any prior). -/
theorem isIC_implies_truthful_bayesNash (M : Mechanism ι) [Finite (∀ i, M.Θ i)]
    (hIC : M.isIC) (μ : PMF (∀ i, M.Θ i)) :
    (M.inducedBayesianGame μ).BayesNash (M.truthful μ) := by
  rw [BayesianGame.bayesNash_iff_exAnteEU]
  intro who s'
  simp only [BayesianGame.exAnteEU, inducedBayesianGame, truthful, ge_iff_le]
  apply Math.ProbabilityMassFunction.expect_mono_of_pointwise
  intro θ
  have happ := M.update_truthful_apply μ who s' θ
  simp only [inducedBayesianGame] at happ
  rw [happ]
  exact hIC who θ (s' (θ who))

/-- *Strategy-proofness* is a synonym for dominant-strategy incentive
compatibility (DSIC), the standard term in mechanism design literature. -/
def isStrategyProof (M : Mechanism ι) : Prop := M.isIC

/-- Strategy-proofness and DSIC are definitionally the same. -/
theorem isStrategyProof_iff_isIC (M : Mechanism ι) :
    M.isStrategyProof ↔ M.isIC := Iff.rfl

/-- *Social welfare* of a mechanism on a report profile is the sum of
players' payoffs (utilitarian aggregate). -/
def socialWelfare [Fintype ι] (M : Mechanism ι) (θ : ∀ i, M.Θ i) : ℝ :=
  ∑ i, M.outcome θ i

/-- A mechanism is *(weakly) individually rational* w.r.t. an outside-option
function `o : ι → ℝ` if every player gets at least `o i` under truthful
reporting, regardless of others' types. -/
def IsIndividuallyRational (M : Mechanism ι) (o : ι → ℝ) : Prop :=
  ∀ (i : ι) (θ : ∀ j, M.Θ j), M.outcome θ i ≥ o i

/-- A mechanism is *(weakly) non-negative* (a standard normalization of
IR with outside option `0`): truthful reporting never costs a player. -/
def IsNonNegative (M : Mechanism ι) : Prop := M.IsIndividuallyRational (fun _ => 0)

/-- Non-negativity is exactly IR with zero outside option. -/
theorem IsNonNegative_iff (M : Mechanism ι) :
    M.IsNonNegative ↔ M.IsIndividuallyRational (fun _ => 0) := Iff.rfl

open Classical in
/-- BIC is implied by BayesNash of truthful reporting (BayesNash is stronger
    since it covers type-dependent deviations, not just constant ones). -/
theorem isBIC_of_truthful_bayesNash (M : Mechanism ι) (μ : PMF (∀ i, M.Θ i))
    (hBN : (M.inducedBayesianGame μ).BayesNash (M.truthful μ)) :
    M.isBIC μ := by
  rw [BayesianGame.bayesNash_iff_exAnteEU] at hBN
  intro who θ'
  have h := hBN who (fun _ => θ')
  simp only [BayesianGame.exAnteEU, inducedBayesianGame, truthful] at h
  convert h using 2
  funext θ
  congr 1
  exact (M.update_truthful_apply μ who (fun _ => θ') θ).symm

end Mechanism

end GameTheory
