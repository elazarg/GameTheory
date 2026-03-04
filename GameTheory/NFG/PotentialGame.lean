import GameTheory.Core.GameProperties
import GameTheory.Concepts.SolutionConcepts
import Math.Probability

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
    Proof: the exact potential property gives `eu_diff = Φ_diff`,
    so `eu_diff > 0 ↔ Φ_diff > 0` follows immediately. -/
theorem IsExactPotential.toOrdinal {G : KernelGame ι} {Φ : Profile G → ℝ}
    (hΦ : G.IsExactPotential Φ) : G.IsOrdinalPotential Φ := by
  intro who σ s'
  have h := hΦ who σ s'
  constructor
  · intro heu
    have : G.eu (Function.update σ who s') who - G.eu σ who > 0 := by
      exact sub_pos.mpr (by simpa [gt_iff_lt] using heu)
    linarith
  · intro hphi
    have : Φ (Function.update σ who s') - Φ σ > 0 := by
      exact sub_pos.mpr (by simpa [gt_iff_lt] using hphi)
    linarith

/-- If `Φ` is an exact potential for `G` and `σ` maximizes `Φ`, then `σ` is Nash.
    Proof: for any deviation `(who, s')`, the potential property gives
    `eu(update) - eu(σ) = Φ(update) - Φ(σ) ≤ 0`, so `eu(σ) ≥ eu(update)`. -/
theorem IsExactPotential.nash_of_maximizer {G : KernelGame ι} {Φ : Profile G → ℝ}
    (hΦ : G.IsExactPotential Φ) {σ : Profile G}
    (hmax : ∀ τ : Profile G, Φ σ ≥ Φ τ) : G.IsNash σ := by
  intro who s'
  have hle := hmax (Function.update σ who s')
  by_contra hnot
  have hgt : G.eu (Function.update σ who s') who > G.eu σ who := by
    linarith
  have hphi : Φ (Function.update σ who s') > Φ σ := by
    have hpot := hΦ who σ s'
    linarith
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
  have hphi := (hΦ who σ s').mp (by simpa [gt_iff_lt] using hdev)
  have hle := hmax (Function.update σ who s')
  linarith

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
    push_neg at h
    have : G.eu (Function.update σ who s') who > G.eu σ who := by
      exact (hΦ who σ s').mpr (by simpa [gt_iff_lt] using h)
    have := hN who s'
    linarith
  · intro hmax who s'
    by_contra h
    push_neg at h
    have : Φ (Function.update σ who s') > Φ σ := by
      exact (hΦ who σ s').mp (by simpa [gt_iff_lt] using h)
    have := hmax who s'
    linarith

end KernelGame
end GameTheory
