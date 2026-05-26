/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameProperties
import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# Potential Games

Theorems linking potential functions to Nash equilibria for kernel-based games.

Provides:
- `IsExactPotential.toOrdinal` — every exact potential is an ordinal potential
- `IsExactPotential.nash_of_maximizer` — a maximizer of an exact potential is Nash
- `IsOrdinalPotential.nash_of_maximizer` — a maximizer of an ordinal potential is Nash
-/

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- An exact potential game is an ordinal potential game.
    The exact-potential identity `eu_diff = Φ_diff` implies `eu_diff > 0 ↔ Φ_diff > 0`. -/
theorem IsExactPotential.toOrdinal {G : KernelGame ι} {Φ : Profile G → ℝ}
    (hΦ : G.IsExactPotential Φ) : G.IsOrdinalPotential Φ := by
  intro who σ s'
  constructor <;> intro h <;> linarith [hΦ who σ s']

/-- If `Φ` is an ordinal potential for `G` and `σ` maximizes `Φ`, then `σ` is Nash.
    Proof: by contradiction. If `σ` is not Nash, some player has a profitable
    deviation, which by the ordinal property would increase `Φ`, contradicting
    maximality. -/
theorem IsOrdinalPotential.nash_of_maximizer {G : KernelGame ι} {Φ : Profile G → ℝ}
    (hΦ : G.IsOrdinalPotential Φ) {σ : Profile G}
    (hmax : ∀ τ : Profile G, Φ σ ≥ Φ τ) : G.IsNash σ := by
  by_contra hnn
  simp only [IsNash, not_forall, not_le] at hnn
  obtain ⟨who, s', hdev⟩ := hnn
  have hphi := (hΦ who σ s').mp (by simpa [gt_iff_lt] using hdev)
  have hle := hmax (Function.update σ who s')
  linarith

/-- If `Φ` is an exact potential for `G` and `σ` maximizes `Φ`, then `σ` is Nash. -/
theorem IsExactPotential.nash_of_maximizer {G : KernelGame ι} {Φ : Profile G → ℝ}
    (hΦ : G.IsExactPotential Φ) {σ : Profile G}
    (hmax : ∀ τ : Profile G, Φ σ ≥ Φ τ) : G.IsNash σ :=
  IsOrdinalPotential.nash_of_maximizer hΦ.toOrdinal hmax

open Classical in
/-- In an ordinal potential game, `σ` is Nash iff `σ` is a local maximizer of `Φ`
    (no single-player deviation increases `Φ`). -/
theorem IsOrdinalPotential.isNash_iff_local_maximizer
    {G : KernelGame ι} {Φ : Profile G → ℝ}
    (hΦ : G.IsOrdinalPotential Φ) {σ : Profile G} :
    G.IsNash σ ↔ ∀ who (s' : G.Strategy who), Φ σ ≥ Φ (Function.update σ who s') := by
  constructor
  · intro hN who s'
    by_contra h
    push Not at h
    have : G.eu (Function.update σ who s') who > G.eu σ who := by
      exact (hΦ who σ s').mpr (by simpa [gt_iff_lt] using h)
    have := hN who s'
    linarith
  · intro hmax who s'
    by_contra h
    push Not at h
    have : Φ (Function.update σ who s') > Φ σ := by
      exact (hΦ who σ s').mp (by simpa [gt_iff_lt] using h)
    have := hmax who s'
    linarith

end KernelGame
end GameTheory
