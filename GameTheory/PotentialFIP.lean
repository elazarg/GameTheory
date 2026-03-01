import GameTheory.PotentialGame

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

variable {ι : Type}

open Classical in
/-- The change in a player's expected utility from a unilateral deviation
    equals the change in the exact potential (direct restatement of the
    potential property, useful as a named lemma). -/
theorem IsExactPotential.eu_diff_eq_potential_diff
    {G : KernelGame ι} {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    (σ : Profile G) (who : ι) (s' : G.Strategy who) :
    G.eu (Function.update σ who s') who - G.eu σ who =
      Φ (Function.update σ who s') - Φ σ :=
  hΦ who σ s'

open Classical in
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

open Classical in
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

open Classical in
/-- If `Φ` is an exact potential and `σ` is the *strict* global maximizer
    (i.e. `Φ σ > Φ τ` for all `τ ≠ σ`), then `σ` is a strict Nash equilibrium. -/
theorem IsExactPotential.strictNash_of_strict_maximizer
    {G : KernelGame ι} {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    {σ : Profile G}
    (hmax : ∀ τ : Profile G, τ ≠ σ → Φ σ > Φ τ) : G.IsStrictNash σ := by
  intro who s' hs'
  have hpot := hΦ who σ s'
  have hne : Function.update σ who s' ≠ σ := by
    intro h
    apply hs'
    have := congr_fun h who
    simpa [Function.update] using this
  have hlt := hmax _ hne
  linarith

open Classical in
/-- In an exact potential game, `σ` is Nash iff `σ` is a local maximizer of `Φ`
    (no single-player deviation increases `Φ`). -/
theorem IsExactPotential.isNash_iff_local_maximizer
    {G : KernelGame ι} {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    {σ : Profile G} :
    G.IsNash σ ↔ ∀ who (s' : G.Strategy who), Φ σ ≥ Φ (Function.update σ who s') := by
  constructor
  · intro hN who s'
    have hpot := hΦ who σ s'
    have hge := hN who s'
    linarith
  · intro hmax who s'
    have hpot := hΦ who σ s'
    have hge := hmax who s'
    linarith

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Nash existence for finite exact potential games.**
    A finite exact potential game always has a Nash equilibrium:
    the profile that maximizes the potential function. -/
theorem IsExactPotential.nash_exists
    {G : KernelGame ι} [Fintype (Profile G)] [Nonempty (Profile G)]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) :
    ∃ σ : Profile G, G.IsNash σ := by
  obtain ⟨σ, _, hmax⟩ := Finset.exists_max_image Finset.univ Φ
    ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  exact ⟨σ, IsExactPotential.nash_of_maximizer hΦ (fun τ => hmax τ (Finset.mem_univ τ))⟩

end KernelGame
end GameTheory
