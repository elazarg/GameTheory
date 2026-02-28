import GameTheory.SolutionConcepts

/-!
# GameTheory.Minimax

Minimax concepts for kernel-based games: guarantees and saddle points.

Provides:
- `KernelGame.Guarantees` — player `who` playing `s` guarantees at least payoff `v`
- `KernelGame.Guarantees.mono` — monotonicity of guarantees in the bound
- `KernelGame.IsSaddlePoint` — saddle point for 2-player games
- `KernelGame.isSaddlePoint_iff_isNash` — saddle point ↔ Nash equilibrium for 2-player games
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

open Classical in
/-- Player `who` playing strategy `s` guarantees at least payoff `v`:
    for every profile `σ`, replacing `who`'s strategy with `s` yields EU ≥ `v`. -/
def Guarantees (G : KernelGame ι) (who : ι) (s : G.Strategy who) (v : ℝ) : Prop :=
  ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥ v

/-- If `s` guarantees `v` and `v' ≤ v`, then `s` also guarantees `v'`. -/
theorem Guarantees.mono {G : KernelGame ι} {who : ι} {s : G.Strategy who}
    {v v' : ℝ} (hv : v' ≤ v) (hg : G.Guarantees who s v) :
    G.Guarantees who s v' :=
  fun σ => le_trans hv (hg σ)

open Classical in
/-- A profile `σ` is a saddle point for a 2-player game if neither player can
    improve by unilateral deviation. -/
def IsSaddlePoint (G : KernelGame (Fin 2)) (σ : Profile G) : Prop :=
  (∀ s₀ : G.Strategy 0, G.eu σ 0 ≥ G.eu (Function.update σ 0 s₀) 0) ∧
  (∀ s₁ : G.Strategy 1, G.eu σ 1 ≥ G.eu (Function.update σ 1 s₁) 1)

/-- In a 2-player game, a profile is a saddle point if and only if it is a Nash equilibrium. -/
theorem isSaddlePoint_iff_isNash (G : KernelGame (Fin 2)) (σ : Profile G) :
    G.IsSaddlePoint σ ↔ G.IsNash σ := by
  constructor
  · intro ⟨h0, h1⟩ who s'
    fin_cases who
    · convert h0 s'
    · convert h1 s'
  · intro hN
    exact ⟨fun s₀ => by convert hN 0 s₀, fun s₁ => by convert hN 1 s₁⟩

end KernelGame

end GameTheory
