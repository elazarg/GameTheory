/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.BestResponse
import GameTheory.Concepts.Equilibrium.ApproximateNash
import Math.Probability

/-!
# Best Response Dynamics

Best response dynamics is a natural process where players iteratively
update their strategies to best-respond to the current profile.

## Main definitions

* `ImprovingDeviation` — a single-player deviation that strictly improves EU
  (structural view)
* `ImprovingStep` — the relational view: `τ` is one improving deviation away from `σ`

## Main results

* `no_improving_deviation_iff_nash` — no improving deviation ⇔ Nash equilibrium
* `improvingStep_iff` — the relational and structural views agree
* `not_isNash_iff_exists_improvingStep` — non-Nash ⇔ an improving step exists
* `strictNash_absorbing` — strict Nash equilibria are absorbing states
* `εNash_bounded_improvement` — in an ε-Nash profile, deviations improve by ≤ ε
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] (G : KernelGame ι)

open Classical in
/-- An improving deviation: player `who` switches from `σ who` to `s'`
    and strictly improves their EU. -/
structure ImprovingDeviation (σ : Profile G) where
  who : ι
  newStrategy : G.Strategy who
  improves : G.eu (Function.update σ who newStrategy) who > G.eu σ who

/-- A Nash equilibrium has no improving deviations. -/
theorem no_improving_deviation_iff_nash {σ : Profile G} :
    IsEmpty (G.ImprovingDeviation σ) ↔ G.IsNash σ := by
  constructor
  · intro hemp who s'
    by_contra h
    push Not at h
    exact (hemp.false ⟨who, s', h⟩).elim
  · intro hN
    constructor
    intro ⟨who, s', himprove⟩
    have := hN who s'
    linarith

open Classical in
/-- An **improving step**: `τ` is obtained from `σ` by a single player's improving
deviation. The relational counterpart of `ImprovingDeviation`, convenient for
reasoning about better-response dynamics as a relation (paths, well-foundedness). -/
def ImprovingStep (σ τ : Profile G) : Prop :=
  ∃ (who : ι) (s' : G.Strategy who),
    τ = Function.update σ who s' ∧ G.eu τ who > G.eu σ who

/-- The relational and structural views agree: an improving step out of `σ` is
exactly an improving deviation applied to `σ`. -/
theorem improvingStep_iff {σ τ : Profile G} :
    G.ImprovingStep σ τ ↔
      ∃ d : G.ImprovingDeviation σ, τ = Function.update σ d.who d.newStrategy := by
  constructor
  · rintro ⟨who, s', rfl, h⟩
    exact ⟨⟨who, s', h⟩, rfl⟩
  · rintro ⟨⟨who, s', h⟩, rfl⟩
    exact ⟨who, s', rfl, h⟩

open Classical in
/-- A profile fails to be Nash exactly when an improving step leaves it. -/
theorem not_isNash_iff_exists_improvingStep {σ : Profile G} :
    ¬ G.IsNash σ ↔ ∃ τ, G.ImprovingStep σ τ := by
  unfold IsNash ImprovingStep
  push Not
  constructor
  · rintro ⟨who, s', h⟩
    exact ⟨Function.update σ who s', who, s', rfl, h⟩
  · rintro ⟨τ, who, s', rfl, h⟩
    exact ⟨who, s', h⟩

open Classical in
/-- A strict Nash equilibrium is absorbing: any single-player deviation
    strictly decreases the deviator's EU. -/
theorem strictNash_absorbing {σ : Profile G} (hstrict : G.IsStrictNash σ) :
    ∀ (who : ι) (s' : G.Strategy who), s' ≠ σ who →
      G.eu (Function.update σ who s') who < G.eu σ who :=
  hstrict

open Classical in
/-- In an ε-Nash equilibrium, any improving deviation must improve by at most ε. -/
theorem εNash_bounded_improvement {ε : ℝ} {σ : Profile G}
    (hε : G.IsεNash ε σ) (who : ι) (s' : G.Strategy who) :
    G.eu (Function.update σ who s') who ≤ G.eu σ who + ε := by
  have := hε who s'
  linarith

end KernelGame

end GameTheory
