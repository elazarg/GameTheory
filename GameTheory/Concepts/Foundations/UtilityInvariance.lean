/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# Utility Invariance

Utility transformations that preserve Nash equilibria.

A per-player positive affine transformation of utilities (each player rescales
by its own `a i > 0` and shifts by its own `b i`) does not change which strategy
profiles are Nash equilibria. This is a fundamental invariance property:
solution concepts depend on the ordinal ranking of outcomes, not on the cardinal
utility scale.
-/

namespace GameTheory

open Math.Probability

variable {ι : Type} [DecidableEq ι]

/-- Each player may apply its own positive affine transform to its utility
without changing the Nash equilibria: if `u' σ i = a i * u σ i + b i` with
`a i > 0`, then a strategy profile is Nash in `ofEU S u` iff it is Nash in
`ofEU S u'`. Positive scaling preserves the direction of every within-player
comparison, and per-player additive constants cancel. -/
theorem ofEU_nash_affine (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (b : ι → ℝ)
    (u' : (∀ i, S i) → Payoff ι)
    (htrans : ∀ σ i, u' σ i = a i * u σ i + b i) (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔ (KernelGame.ofEU S u').IsNash σ := by
  classical
  simp only [KernelGame.IsNash, KernelGame.eu_ofEU, KernelGame.ofEU_Strategy]
  constructor
  · intro hN who s'
    have := hN who s'
    rw [htrans σ who, htrans (Function.update σ who s') who]
    nlinarith [ha who]
  · intro hN who s'
    have := hN who s'
    rw [htrans σ who, htrans (Function.update σ who s') who] at this
    nlinarith [ha who]

/-- Each player's own positive affine transform of utilities preserves dominant
strategies, by the same argument as `ofEU_nash_affine`. -/
theorem ofEU_isDominant_affine (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (b : ι → ℝ)
    (u' : (∀ i, S i) → Payoff ι)
    (htrans : ∀ σ i, u' σ i = a i * u σ i + b i) (who : ι) (s : S who) :
    (KernelGame.ofEU S u).IsDominant who s ↔ (KernelGame.ofEU S u').IsDominant who s := by
  classical
  simp only [KernelGame.IsDominant, KernelGame.eu_ofEU, KernelGame.ofEU_Strategy]
  constructor
  · intro hd σ s'
    have := hd σ s'
    rw [htrans (Function.update σ who s) who, htrans (Function.update σ who s') who]
    nlinarith [ha who]
  · intro hd σ s'
    have := hd σ s'
    rw [htrans (Function.update σ who s) who, htrans (Function.update σ who s') who] at this
    nlinarith [ha who]

/-- Adding a per-player constant to utilities preserves Nash equilibria.

This is the special case of `ofEU_nash_affine` with `a i = 1`: player-specific
constants cancel in any utility comparison within a single player's deviations. -/
theorem ofEU_nash_shift (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (b : ι → ℝ)
    (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔
    (KernelGame.ofEU S (fun τ i => u τ i + b i)).IsNash σ :=
  ofEU_nash_affine S u (fun _ => 1) (fun _ => one_pos) b _ (fun _ _ => by ring) σ

/-- Positive scaling of utilities preserves Nash equilibria.

This is the special case of `ofEU_nash_affine` with `b = 0`: multiplying all
utilities by a positive constant preserves the direction of every inequality. -/
theorem ofEU_nash_scale (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (a : ℝ) (ha : a > 0) (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔
    (KernelGame.ofEU S (fun τ i => a * u τ i)).IsNash σ :=
  ofEU_nash_affine S u (fun _ => a) (fun _ => ha) (fun _ => 0) _ (fun _ _ => by ring) σ

end GameTheory
