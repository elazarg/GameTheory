/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Mathlib.Data.Fintype.Basic

/-!
# Principal–agent contracts (hidden action / moral hazard)

The principal–agent *hidden-action* model, the object of algorithmic contract
theory (Dütting–Feldman–Talgam-Cohen, *Algorithmic Contract Theory: A Survey*,
2024). An agent privately chooses one of finitely many `Action`s; each action
induces a distribution over a finite set of `Outcome`s and carries a private
effort `cost`. The principal observes only the realized outcome, collects a
`reward`, and commits in advance to an outcome-contingent `payment` (the
*contract*). Under **limited liability** payments are nonnegative.

The agent is **risk-neutral** (utility is linear in the payment), as in the
algorithmic contract-theory literature; classical Holmström moral hazard instead
assumes a concave agent utility of money.

This is the discrete/`PMF` foundation of the contract-theory layer. Optimality
results (linear contracts max-min optimal under mean-only knowledge; budget-
optimal threshold = Neyman–Pearson) build on these and are left to follow-on files.

## Main definitions

* `PrincipalAgent` — a hidden-action environment
* `PrincipalAgent.agentUtility` / `principalUtility` / `expectedReward`
* `PrincipalAgent.LimitedLiability` — a nonnegative payment scheme
* `PrincipalAgent.IsIncentivized` — the agent's utility-maximizing action
* `PrincipalAgent.linearPayment` — the linear (commission) contract

## Main results

* `principalUtility_add_agentUtility` — utilities sum to the social surplus
* `agentUtility_ge` — limited liability bounds the agent's utility below by `-cost`
* `exists_incentivized` — with finitely many actions, an incentivized action exists
* `agentUtility_linearPayment` — agent utility under a linear contract
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

/-- A principal–agent (hidden-action / moral-hazard) environment: each `Action`
the agent might take induces a distribution over `Outcome`s and costs the agent
`cost a`; the principal's gross payoff at an outcome is `reward`. -/
structure PrincipalAgent (Action Outcome : Type) where
  /-- The distribution over outcomes induced by each action. -/
  outcomeDist : Action → PMF Outcome
  /-- The principal's gross reward at each outcome. -/
  reward : Outcome → ℝ
  /-- The agent's private effort cost of each action. -/
  cost : Action → ℝ

namespace PrincipalAgent

section ExpectHelpers

variable {Outcome : Type} [Finite Outcome]

private theorem expect_sub (d : PMF Outcome) (f g : Outcome → ℝ) :
    expect d (fun o => f o - g o) = expect d f - expect d g := by
  letI : Fintype Outcome := Fintype.ofFinite Outcome
  rw [expect_eq_sum, expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun o _ => by ring)

private theorem expect_const_mul (d : PMF Outcome) (c : ℝ) (f : Outcome → ℝ) :
    expect d (fun o => c * f o) = c * expect d f := by
  letI : Fintype Outcome := Fintype.ofFinite Outcome
  rw [expect_eq_sum, expect_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun o _ => by ring)

private theorem expect_nonneg (d : PMF Outcome) (f : Outcome → ℝ)
    (hf : ∀ o, 0 ≤ f o) : 0 ≤ expect d f := by
  letI : Fintype Outcome := Fintype.ofFinite Outcome
  rw [expect_eq_sum]
  exact Finset.sum_nonneg (fun o _ => mul_nonneg ENNReal.toReal_nonneg (hf o))

end ExpectHelpers

variable {Action Outcome : Type} [Finite Outcome] (I : PrincipalAgent Action Outcome)

/-- The agent's expected utility from action `a` under payment scheme `t`:
expected payment received, minus the action's cost. -/
noncomputable def agentUtility (t : Outcome → ℝ) (a : Action) : ℝ :=
  expect (I.outcomeDist a) t - I.cost a

/-- The principal's expected utility when the agent plays `a` under payment `t`:
the expected reward net of the payment. -/
noncomputable def principalUtility (t : Outcome → ℝ) (a : Action) : ℝ :=
  expect (I.outcomeDist a) (fun o => I.reward o - t o)

/-- The expected gross reward of action `a`. -/
noncomputable def expectedReward (a : Action) : ℝ :=
  expect (I.outcomeDist a) I.reward

/-- A linear (commission) contract: the agent receives a fixed fraction `α` of
the realized reward. -/
def linearPayment (α : ℝ) : Outcome → ℝ := fun o => α * I.reward o

/-- Limited liability: payments are nonnegative (the agent is never charged). -/
def LimitedLiability (t : Outcome → ℝ) : Prop := ∀ o, 0 ≤ t o

/-- Action `a` is incentive compatible under payment `t` if it maximizes the
agent's expected utility. -/
def IsIncentivized (t : Outcome → ℝ) (a : Action) : Prop :=
  ∀ a', I.agentUtility t a' ≤ I.agentUtility t a

/-- **Welfare identity.** The principal's and the agent's expected utilities sum
to the realized social surplus (expected reward minus effort cost), regardless of
the payment scheme `t`: a contract *splits* surplus, it does not create or
destroy it. -/
theorem principalUtility_add_agentUtility (t : Outcome → ℝ) (a : Action) :
    I.principalUtility t a + I.agentUtility t a = I.expectedReward a - I.cost a := by
  simp only [principalUtility, agentUtility, expectedReward]
  rw [expect_sub (I.outcomeDist a) I.reward t]
  ring

/-- **Limited liability protects the agent.** Under a nonnegative payment scheme
the agent's utility is at least `-cost a`: its expected payment is nonnegative, so
it can lose at most its effort cost. -/
theorem agentUtility_ge (t : Outcome → ℝ) (ht : LimitedLiability t) (a : Action) :
    -I.cost a ≤ I.agentUtility t a := by
  have h : 0 ≤ expect (I.outcomeDist a) t := expect_nonneg _ t ht
  simp only [agentUtility]
  linarith

omit [Finite Outcome] in
/-- A linear contract with a nonnegative commission rate on a nonnegative reward
satisfies limited liability. -/
theorem linearPayment_limitedLiability {α : ℝ} (hα : 0 ≤ α)
    (hr : ∀ o, 0 ≤ I.reward o) : LimitedLiability (I.linearPayment α) :=
  fun o => mul_nonneg hα (hr o)

/-- Under a linear contract the agent's expected utility is
`α · (expected reward) − cost`. -/
theorem agentUtility_linearPayment (α : ℝ) (a : Action) :
    I.agentUtility (I.linearPayment α) a = α * I.expectedReward a - I.cost a := by
  unfold agentUtility expectedReward linearPayment
  rw [expect_const_mul (I.outcomeDist a) α I.reward]

omit [Finite Outcome] in
/-- **Existence of a best response.** With finitely many possible actions the
agent has an incentive-compatible (expected-utility-maximizing) action against any
payment scheme. -/
theorem exists_incentivized [Finite Action] [Nonempty Action] (t : Outcome → ℝ) :
    ∃ a, I.IsIncentivized t a := by
  obtain ⟨a, ha⟩ := Finite.exists_max (I.agentUtility t)
  exact ⟨a, ha⟩

end PrincipalAgent

end GameTheory
