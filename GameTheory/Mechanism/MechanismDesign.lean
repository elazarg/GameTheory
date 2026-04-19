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
/-- Dominant-strategy IC implies truthful reporting is a Bayes-Nash
    equilibrium of the induced game (for any prior). -/
theorem isIC_implies_truthful_bayesNash (M : Mechanism ι) (hIC : M.isIC)
    (μ : PMF (∀ i, M.Θ i)) :
    (M.inducedBayesianGame μ).BayesNash (M.truthful μ) := by
  rw [BayesianGame.bayesNash_iff_exAnteEU]
  intro who s'
  simp only [BayesianGame.exAnteEU, inducedBayesianGame, truthful, ge_iff_le]
  apply Math.ProbabilityMassFunction.expect_mono_of_pointwise
  intro θ
  -- Need: M.outcome (fun i => update (truthful) who s' i (θ i)) who ≤ M.outcome θ who
  -- update (truthful) who s' i (θ i) = if i = who then s'(θ who) else θ i
  -- This matches Function.update θ who (s' (θ who))
  have : (fun i => Function.update (M.truthful μ) who s' i (θ i)) =
      Function.update θ who (s' (θ who)) := by
    ext i
    by_cases hi : i = who
    · subst hi
      simp [Function.update]
    · simp [truthful, Function.update, hi]
  simp only [inducedBayesianGame] at this
  rw [this]
  exact hIC who θ (s' (θ who))

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
  -- The LHS of h matches, need to show RHS matches
  -- update (fun θ => θ) who (fun _ => θ') applied to θ gives update θ who θ'
  convert h using 2
  ext θ
  congr 1
  ext i
  by_cases hi : i = who
  · subst hi
    simp [Function.update]
  · simp [truthful, Function.update, hi]

end Mechanism

end GameTheory
