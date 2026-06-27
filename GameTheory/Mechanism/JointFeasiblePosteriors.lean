/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.FeasiblePosteriors

/-!
# Feasible joint posterior beliefs

The multi-agent counterpart of `FeasiblePosteriors`: several agents each receive
private information about a common state and form a posterior, and we ask which
*joint* distributions over the agents' posteriors are feasible (inducible by a
common-prior information structure). This is the object of Arieli–Babichenko–
Sandomirskiy–Tamuz, *Feasible Joint Posterior Beliefs*, JPE 2021.

A belief profile is `ι → PMF Ω` (agent `i`'s belief). A joint distribution over
profiles is `τ : PMF (ι → PMF Ω)`. Feasibility is modeled, as in the single-agent
case, by a **coupling** of the state with the belief profile in which each agent is
self-consistent (the agent-`i` projection is the canonical single-agent coupling of
agent `i`'s marginal).

## Main definitions

* `agentMarginal τ i` — agent `i`'s marginal distribution over their own posterior
* `IsJointBayesPlausible prior τ` — every agent's marginal is Bayes plausible
* `IsJointFeasible prior τ` — `τ` is realized by a self-consistent common-prior coupling

## Main results

* `IsJointFeasible.bayesPlausible_agentMarginal` — **feasible ⇒ every marginal Bayes plausible**
* `IsJointFeasible.isJointBayesPlausible` — the corollary at the profile level
* `isJointFeasible_uninformative` — the uninformative experiment is jointly feasible (non-vacuity)

The *converse* — that marginal (even joint) Bayes plausibility is *sufficient* for
feasibility — is **false for two or more agents** and the full characterization is the
hard content of Arieli–Babichenko–Sandomirskiy–Tamuz; it is **not** formalized here.
-/

namespace GameTheory

open Math.Probability

variable {ι Ω : Type}

/-- Agent `i`'s marginal distribution over their own posterior belief. -/
noncomputable def agentMarginal (τ : PMF (ι → PMF Ω)) (i : ι) : PMF (PMF Ω) :=
  τ.map fun p => p i

/-- A canonical single-agent coupling of a point-mass belief distribution. -/
theorem posteriorCoupling_pure (b : PMF Ω) :
    posteriorCoupling (PMF.pure b) = b.map fun ω => (ω, b) := by
  unfold posteriorCoupling
  rw [PMF.pure_bind]

/-- A joint distribution over belief profiles is *jointly Bayes plausible* if every
agent's marginal posterior distribution is Bayes plausible. Necessary for
feasibility, but — for two or more agents — not sufficient. -/
def IsJointBayesPlausible (prior : PMF Ω) (τ : PMF (ι → PMF Ω)) : Prop :=
  ∀ i, IsBayesPlausible prior (agentMarginal τ i)

/-- A joint distribution over belief profiles is *feasible* from `prior` if it is
realized by a common-prior experiment: a coupling `C` of the state with the belief
profile whose state marginal is `prior`, whose profile marginal is `τ`, and in which
each agent is self-consistent — the agent-`i` projection `(state, beliefᵢ)` is the
canonical single-agent coupling of agent `i`'s marginal (so, conditional on agent
`i`'s belief `b`, the state is distributed as `b`). -/
def IsJointFeasible (prior : PMF Ω) (τ : PMF (ι → PMF Ω)) : Prop :=
  ∃ C : PMF (Ω × (ι → PMF Ω)),
    C.map Prod.fst = prior ∧
    C.map Prod.snd = τ ∧
    ∀ i, C.map (fun x => (x.1, x.2 i)) = posteriorCoupling (agentMarginal τ i)

/-- **Feasibility forces marginal Bayes plausibility.** In any feasible joint
distribution, each agent's marginal posterior distribution is Bayes plausible — its
average belief is the prior. (The converse fails for two or more agents.) -/
theorem IsJointFeasible.bayesPlausible_agentMarginal {prior : PMF Ω}
    {τ : PMF (ι → PMF Ω)} (h : IsJointFeasible prior τ) (i : ι) :
    IsBayesPlausible prior (agentMarginal τ i) := by
  obtain ⟨C, hfst, _, hconsist⟩ := h
  unfold IsBayesPlausible
  rw [← posteriorCoupling_fst (agentMarginal τ i), ← hconsist i, PMF.map_comp]
  exact hfst

/-- Every agent's marginal in a feasible joint distribution is Bayes plausible. -/
theorem IsJointFeasible.isJointBayesPlausible {prior : PMF Ω}
    {τ : PMF (ι → PMF Ω)} (h : IsJointFeasible prior τ) :
    IsJointBayesPlausible prior τ :=
  fun i => h.bayesPlausible_agentMarginal i

/-- The uninformative experiment — no agent learns anything, so every agent's belief
is the prior — is jointly feasible. (Witnesses that `IsJointFeasible` is satisfiable.) -/
theorem isJointFeasible_uninformative (prior : PMF Ω) :
    IsJointFeasible prior (PMF.pure fun _ : ι => prior) := by
  refine ⟨prior.map fun ω => (ω, fun _ => prior), ?_, ?_, fun i => ?_⟩
  · rw [PMF.map_comp]
    exact PMF.map_id prior
  · rw [PMF.map_comp]
    conv_lhs =>
      change prior.map (Function.const Ω (fun _ : ι => prior))
    rw [PMF.map_const]
  · have hmarg : agentMarginal (PMF.pure fun _ : ι => prior) i = PMF.pure prior := by
      simp only [agentMarginal, PMF.pure_map]
    rw [hmarg, posteriorCoupling_pure, PMF.map_comp]
    rfl

end GameTheory
