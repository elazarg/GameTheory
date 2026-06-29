/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import GameTheory.Core.GameForm
import Math.Probability

/-!
# GameTheory.Core.GameProperties
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- Profile `σ` Pareto-dominates profile `τ`. -/
def ParetoDominates (G : KernelGame ι) (σ τ : Profile G) : Prop :=
  (∀ i : ι, G.eu σ i ≥ G.eu τ i) ∧ ∃ i : ι, G.eu σ i > G.eu τ i

/-- Profile `σ` is Pareto-efficient (no Pareto improvement exists). -/
def IsParetoEfficient (G : KernelGame ι) (σ : Profile G) : Prop :=
  ¬ ∃ τ : Profile G, G.ParetoDominates τ σ

/-- Individual rationality w.r.t. reservation utility `r`. -/
def IsIndividuallyRational (G : KernelGame ι)
    (r : ι → ℝ) (σ : Profile G) : Prop :=
  ∀ i : ι, G.eu σ i ≥ r i

/-- Exact potential game (in expected-utility form). -/
def IsExactPotential (G : KernelGame ι) [DecidableEq ι] (Φ : Profile G → ℝ) : Prop :=
  ∀ (who : ι) (σ : Profile G) (s' : G.Strategy who),
    G.eu (Function.update σ who s') who - G.eu σ who =
      (Φ (Function.update σ who s') - Φ σ)

/-- Weighted exact potential game (in expected-utility form).

The positive weight `w who` scales player `who`'s utility difference relative to
the common potential difference. -/
def IsWeightedExactPotential (G : KernelGame ι) [DecidableEq ι]
    (Φ : Profile G → ℝ) (w : ι → ℝ) : Prop :=
  (∀ who : ι, 0 < w who) ∧
    ∀ (who : ι) (σ : Profile G) (s' : G.Strategy who),
      G.eu (Function.update σ who s') who - G.eu σ who =
        w who * (Φ (Function.update σ who s') - Φ σ)

/-- Exact potentials are weighted exact potentials with all weights equal to
one. -/
theorem IsExactPotential.toWeightedExactPotential
    {G : KernelGame ι} [DecidableEq ι] {Φ : Profile G → ℝ}
    (hΦ : G.IsExactPotential Φ) :
    G.IsWeightedExactPotential Φ (fun _ => 1) := by
  refine ⟨fun _ => zero_lt_one, ?_⟩
  intro who σ s'
  simpa using hΦ who σ s'

/-- Ordinal potential game (in expected-utility form). -/
def IsOrdinalPotential (G : KernelGame ι) [DecidableEq ι] (Φ : Profile G → ℝ) : Prop :=
  ∀ (who : ι) (σ : Profile G) (s' : G.Strategy who),
    (G.eu (Function.update σ who s') who > G.eu σ who) ↔
      (Φ (Function.update σ who s') > Φ σ)

/-- Team game / identical-interest property at the outcome-utility level. -/
def IsTeamGame (G : KernelGame ι) : Prop :=
  ∀ (ω : G.Outcome) (i j : ι), G.utility ω i = G.utility ω j

section FinitePlayers

variable [Fintype ι]

/-- Social welfare at profile `σ` as sum of expected utilities. -/
noncomputable def socialWelfare (G : KernelGame ι) (σ : Profile G) : ℝ :=
  ∑ i : ι, G.eu σ i

/-- Constant-sum game property at the outcome-utility level. -/
def IsConstantSum (G : KernelGame ι) (c : ℝ) : Prop :=
  ∀ ω : G.Outcome, (∑ i : ι, G.utility ω i) = c

/-- Zero-sum game property at the outcome-utility level. -/
def IsZeroSum (G : KernelGame ι) : Prop :=
  G.IsConstantSum 0

end FinitePlayers

end KernelGame

end GameTheory
