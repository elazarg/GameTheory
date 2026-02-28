import GameTheory.GameProperties
import GameTheory.SolutionConcepts

/-!
# Potential Games

Theorems linking potential functions to Nash equilibria for kernel-based games.

Provides:
- `IsExactPotential.toOrdinal` — every exact potential is an ordinal potential
- `IsExactPotential.nash_of_maximizer` — a maximizer of an exact potential is Nash
- `IsOrdinalPotential.nash_of_maximizer` — a maximizer of an ordinal potential is Nash
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- An exact potential game is an ordinal potential game.
    Proof: the exact potential property gives `eu_diff = Φ_diff`,
    so `eu_diff > 0 ↔ Φ_diff > 0` follows immediately. -/
theorem IsExactPotential.toOrdinal {G : KernelGame ι} {Φ : Profile G → ℝ}
    (hΦ : G.IsExactPotential Φ) : G.IsOrdinalPotential Φ := by
  intro who σ s'
  have h := hΦ who σ s'
  constructor
  · intro heu
    have : G.eu (Function.update σ who s') who - G.eu σ who > 0 := sub_pos.mpr heu
    linarith
  · intro hphi
    have : Φ (Function.update σ who s') - Φ σ > 0 := sub_pos.mpr hphi
    linarith

/-- If `Φ` is an exact potential for `G` and `σ` maximizes `Φ`, then `σ` is Nash.
    Proof: for any deviation `(who, s')`, the potential property gives
    `eu(update) - eu(σ) = Φ(update) - Φ(σ) ≤ 0`, so `eu(σ) ≥ eu(update)`. -/
theorem IsExactPotential.nash_of_maximizer {G : KernelGame ι} {Φ : Profile G → ℝ}
    (hΦ : G.IsExactPotential Φ) {σ : Profile G}
    (hmax : ∀ τ : Profile G, Φ σ ≥ Φ τ) : G.IsNash σ := by
  intro who s'
  have hpot := hΦ who σ s'
  have hle := hmax (Function.update σ who s')
  linarith

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
  have hphi := (hΦ who σ s').mp hdev
  have hle := hmax (Function.update σ who s')
  linarith

end KernelGame
end GameTheory
