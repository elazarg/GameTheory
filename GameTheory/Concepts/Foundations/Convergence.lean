/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability

/-!
# Convergence Predicates

Small, reusable convergence predicates for game-theoretic limit notions.

The library does not currently equip `PMF α` with a bundled topology, so PMF
convergence is stated explicitly as pointwise convergence of probability
weights in `ENNReal`. Higher-level objects then assemble their own pointwise
convergence from component convergence relations.
-/

namespace PMF

/-- A PMF has full support when every point receives nonzero probability. -/
def FullSupport {α : Type*} (μ : PMF α) : Prop :=
  ∀ a : α, μ a ≠ 0

theorem FullSupport.apply {α : Type*} {μ : PMF α}
    (h : PMF.FullSupport μ) (a : α) : μ a ≠ 0 :=
  h a

end PMF

namespace GameTheory

open Filter

/-- Pointwise convergence of a sequence of functions. -/
def FunctionConvergesPointwise {α β : Type*} [TopologicalSpace β]
    (fs : ℕ → α → β) (f : α → β) : Prop :=
  ∀ a : α, Tendsto (fun n : ℕ => fs n a) atTop (nhds (f a))

/-- Pointwise convergence of probability mass functions, stated as convergence
of every probability weight in `ENNReal`. -/
def PMFConvergesPointwise {α : Type*} (μs : ℕ → PMF α) (μ : PMF α) : Prop :=
  FunctionConvergesPointwise (fun n a => μs n a) (fun a => μ a)

/-- Pointwise convergence of dependent profiles, parameterized by the
coordinate-level convergence relation. -/
def ProfileConvergesWith {ι : Type*} {Strategy : ι → Type*}
    (Converges : ∀ i : ι, (ℕ → Strategy i) → Strategy i → Prop)
    (σs : ℕ → ∀ i, Strategy i) (σ : ∀ i, Strategy i) : Prop :=
  ∀ i : ι, Converges i (fun n => σs n i) (σ i)

theorem PMFConvergesPointwise.apply {α : Type*} {μs : ℕ → PMF α} {μ : PMF α}
    (h : PMFConvergesPointwise μs μ) (a : α) :
    Tendsto (fun n : ℕ => μs n a) atTop (nhds (μ a)) :=
  h a

theorem ProfileConvergesWith.apply {ι : Type*} {Strategy : ι → Type*}
    {Converges : ∀ i : ι, (ℕ → Strategy i) → Strategy i → Prop}
    {σs : ℕ → ∀ i, Strategy i} {σ : ∀ i, Strategy i}
    (h : ProfileConvergesWith Converges σs σ) (i : ι) :
    Converges i (fun n => σs n i) (σ i) :=
  h i

end GameTheory
