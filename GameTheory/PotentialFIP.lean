import GameTheory.GameProperties
import GameTheory.SolutionConcepts

/-!
# Finite Improvement Property for Potential Games

Key lemmas connecting exact potential functions to the finite improvement
property (FIP).  In an exact potential game every "improving" unilateral
deviation (one that strictly raises the deviator's expected utility) also
strictly raises the potential.  Because the potential is a real-valued
function on the (finite) strategy space, no infinite sequence of improving
deviations can exist — this is the FIP.

Provides:
- `IsExactPotential.eu_diff_eq_potential_diff` — EU change equals potential change
- `IsExactPotential.improving_deviation_increases_potential` — an improving
  deviation strictly increases the potential
- `IsExactPotential.no_improving_at_maximizer` — at a potential maximizer no
  player has a strictly improving deviation
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- The change in a player's expected utility from a unilateral deviation
    equals the change in the exact potential (direct restatement of the
    potential property, useful as a named lemma). -/
theorem IsExactPotential.eu_diff_eq_potential_diff
    {G : KernelGame ι} {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    (σ : Profile G) (who : ι) (s' : G.Strategy who) :
    G.eu (Function.update σ who s') who - G.eu σ who =
      Φ (Function.update σ who s') - Φ σ :=
  hΦ who σ s'

/-- If a player deviates and strictly improves their expected utility,
    the exact potential strictly increases.

    Proof: the potential property gives
    `eu(update) − eu(σ) = Φ(update) − Φ(σ)`.
    The left-hand side is positive by hypothesis, so the right-hand side
    is positive as well. -/
theorem IsExactPotential.improving_deviation_increases_potential
    {G : KernelGame ι} {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    {σ : Profile G} {who : ι} {s' : G.Strategy who}
    (himprove : G.eu (Function.update σ who s') who > G.eu σ who) :
    Φ (Function.update σ who s') > Φ σ := by
  have hpot := hΦ who σ s'
  linarith

/-- At a global maximizer of the exact potential, no player has a strictly
    improving unilateral deviation.

    Proof: the potential property gives
    `eu(update) − eu(σ) = Φ(update) − Φ(σ) ≤ 0`
    (the last inequality by maximality), so `eu(σ) ≥ eu(update)`. -/
theorem IsExactPotential.no_improving_at_maximizer
    {G : KernelGame ι} {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    {σ : Profile G} (hmax : ∀ τ, Φ σ ≥ Φ τ)
    (who : ι) (s' : G.Strategy who) :
    G.eu σ who ≥ G.eu (Function.update σ who s') who := by
  have hpot := hΦ who σ s'
  have hle := hmax (Function.update σ who s')
  linarith

end KernelGame
end GameTheory
