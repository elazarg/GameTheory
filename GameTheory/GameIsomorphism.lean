import GameTheory.SolutionConcepts

/-!
# GameTheory.GameIsomorphism

Utility transformations that preserve Nash equilibria.

An affine transformation of utilities (positive scaling plus per-player shift)
does not change which strategy profiles are Nash equilibria.  This is a
fundamental invariance property: solution concepts depend on the *ordinal*
ranking of outcomes, not on the cardinal utility scale.

## Main results

- `ofEU_nash_affine` — affine transformation `u' σ i = a * u σ i + b i` with
  `a > 0` preserves Nash equilibria
- `ofEU_nash_shift` — adding a per-player constant preserves Nash equilibria
  (special case of affine with `a = 1`)
- `ofEU_nash_scale` — positive scaling preserves Nash equilibria
  (special case of affine with `b = 0`)
-/

namespace GameTheory

variable {ι : Type}

/-- Affine transformation of utilities preserves Nash equilibria.

If `u' σ i = a * u σ i + b i` with `a > 0`, then a strategy profile is Nash
in `ofEU S u` if and only if it is Nash in `ofEU S u'`.  Intuitively, positive
scaling preserves the direction of all utility comparisons, and per-player
additive constants cancel in any within-player comparison. -/
theorem ofEU_nash_affine (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (a : ℝ) (ha : a > 0) (b : ι → ℝ)
    (u' : (∀ i, S i) → Payoff ι)
    (htrans : ∀ σ i, u' σ i = a * u σ i + b i) (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔ (KernelGame.ofEU S u').IsNash σ := by
  classical
  simp only [KernelGame.IsNash, KernelGame.eu_ofEU]
  constructor
  · intro hN who s'
    have := hN who s'
    rw [htrans σ who, htrans (Function.update σ who s') who]
    nlinarith
  · intro hN who s'
    have := hN who s'
    rw [htrans σ who, htrans (Function.update σ who s') who] at this
    nlinarith

/-- Adding a per-player constant to utilities preserves Nash equilibria.

This is the special case of `ofEU_nash_affine` with `a = 1`: player-specific
constants cancel in any utility comparison within a single player's deviations. -/
theorem ofEU_nash_shift (S : ι → Type) (u : (∀ i, S i) → Payoff ι) (b : ι → ℝ)
    (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔
    (KernelGame.ofEU S (fun τ i => u τ i + b i)).IsNash σ := by
  simp only [KernelGame.IsNash, KernelGame.eu_ofEU]
  constructor
  · intro hN who s'; have := hN who s'; linarith
  · intro hN who s'; have := hN who s'; linarith

/-- Positive scaling of utilities preserves Nash equilibria.

This is the special case of `ofEU_nash_affine` with `b = 0`: multiplying all
utilities by a positive constant preserves the direction of every inequality. -/
theorem ofEU_nash_scale (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (a : ℝ) (ha : a > 0) (σ : ∀ i, S i) :
    (KernelGame.ofEU S u).IsNash σ ↔
    (KernelGame.ofEU S (fun τ i => a * u τ i)).IsNash σ := by
  simp only [KernelGame.IsNash, KernelGame.eu_ofEU]
  constructor
  · intro hN who s'; have := hN who s'; nlinarith
  · intro hN who s'; have := hN who s'; nlinarith

end GameTheory
