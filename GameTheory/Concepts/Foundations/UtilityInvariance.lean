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

An affine transformation of utilities (positive scaling plus per-player shift)
does not change which strategy profiles are Nash equilibria. This is a
fundamental invariance property: solution concepts depend on the ordinal
ranking of outcomes, not on the cardinal utility scale.
-/

namespace GameTheory

open Math.Probability

variable {ι : Type} [DecidableEq ι]

/-- Affine transformation of utilities preserves Nash equilibria.

If `u' σ i = a * u σ i + b i` with `a > 0`, then a strategy profile is Nash
in `ofEU S u` if and only if it is Nash in `ofEU S u'`. Intuitively, positive
scaling preserves the direction of all utility comparisons, and per-player
additive constants cancel in any within-player comparison. -/
theorem ofEU_nash_affine (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (a : ℝ) (ha : a > 0) (b : ι → ℝ)
    (u' : (∀ i, S i) → Payoff ι)
    (htrans : ∀ σ i, u' σ i = a * u σ i + b i) (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔ (KernelGame.ofEU S u').IsNash σ := by
  classical
  simp only [KernelGame.IsNash, KernelGame.eu_ofEU, KernelGame.ofEU_Strategy]
  constructor
  · intro hN who s'
    have := hN who s'
    rw [htrans σ who, htrans (Function.update σ who s') who]
    nlinarith
  · intro hN who s'
    have := hN who s'
    rw [htrans σ who, htrans (Function.update σ who s') who] at this
    nlinarith

/-- Affine transformation of utilities preserves dominant strategies, by the
same argument as `ofEU_nash_affine`: positive scaling preserves the direction of
every within-player comparison and per-player shifts cancel. -/
theorem ofEU_isDominant_affine (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (a : ℝ) (ha : a > 0) (b : ι → ℝ)
    (u' : (∀ i, S i) → Payoff ι)
    (htrans : ∀ σ i, u' σ i = a * u σ i + b i) (who : ι) (s : S who) :
    (KernelGame.ofEU S u).IsDominant who s ↔ (KernelGame.ofEU S u').IsDominant who s := by
  classical
  simp only [KernelGame.IsDominant, KernelGame.eu_ofEU, KernelGame.ofEU_Strategy]
  constructor
  · intro hd σ s'
    have := hd σ s'
    rw [htrans (Function.update σ who s) who, htrans (Function.update σ who s') who]
    nlinarith
  · intro hd σ s'
    have := hd σ s'
    rw [htrans (Function.update σ who s) who, htrans (Function.update σ who s') who] at this
    nlinarith

/-- Adding a per-player constant to utilities preserves Nash equilibria.

This is the special case of `ofEU_nash_affine` with `a = 1`: player-specific
constants cancel in any utility comparison within a single player's deviations. -/
theorem ofEU_nash_shift (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (b : ι → ℝ)
    (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔
    (KernelGame.ofEU S (fun τ i => u τ i + b i)).IsNash σ :=
  ofEU_nash_affine S u 1 one_pos b _ (fun _ _ => by ring) σ

/-- Positive scaling of utilities preserves Nash equilibria.

This is the special case of `ofEU_nash_affine` with `b = 0`: multiplying all
utilities by a positive constant preserves the direction of every inequality. -/
theorem ofEU_nash_scale (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (a : ℝ) (ha : a > 0) (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔
    (KernelGame.ofEU S (fun τ i => a * u τ i)).IsNash σ :=
  ofEU_nash_affine S u a ha (fun _ => 0) _ (fun _ _ => by ring) σ

end GameTheory
