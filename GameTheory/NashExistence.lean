import GameTheory.SolutionConcepts
import GameTheory.PotentialGame
import Mathlib.Data.Finset.Max

/-!
# Nash Equilibrium Existence Theorems

Sufficient conditions for the existence of a Nash equilibrium in kernel-based games.

Provides:
- `nash_of_all_have_dominant` — if every player has a dominant strategy, a Nash equilibrium exists
- `exact_potential_nash_exists` — if a finite game has an exact potential, a Nash equilibrium exists
- `ofEU_nash_of_dominant` — specialization of `nash_of_all_have_dominant` to `ofEU` games
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- If every player has a dominant strategy, the profile of dominant strategies
    is a Nash equilibrium. Constructs the profile via `Classical.choice`. -/
theorem nash_of_all_have_dominant {G : KernelGame ι}
    (h : ∀ i, ∃ s : G.Strategy i, G.IsDominant i s) :
    ∃ σ : Profile G, G.IsNash σ := by
  classical
  let σ : Profile G := fun i => (h i).choose
  exact ⟨σ, KernelGame.dominant_is_nash G σ (fun i => (h i).choose_spec)⟩

/-- A finite game with an exact potential function has a Nash equilibrium:
    the profile maximizing the potential. -/
theorem exact_potential_nash_exists {G : KernelGame ι}
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    [Fintype (Profile G)] [Nonempty (Profile G)] :
    ∃ σ : Profile G, G.IsNash σ := by
  obtain ⟨σ_max, _, hmax⟩ :=
    Finset.exists_max_image Finset.univ Φ Finset.univ_nonempty
  exact ⟨σ_max, hΦ.nash_of_maximizer (fun τ => hmax τ (Finset.mem_univ τ))⟩

/-- For `ofEU` games: if every player has a dominant strategy, a Nash equilibrium exists. -/
theorem ofEU_nash_of_dominant (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (h : ∀ i, ∃ s : S i, (KernelGame.ofEU S u).IsDominant i s) :
    ∃ σ : ∀ i, S i, (KernelGame.ofEU S u).IsNash σ := by
  classical
  let G := KernelGame.ofEU S u
  let σ : Profile G := fun i => (h i).choose
  exact ⟨σ, KernelGame.dominant_is_nash G σ (fun i => (h i).choose_spec)⟩

end KernelGame
end GameTheory
