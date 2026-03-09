import GameTheory.Core.GameProperties
import Math.Probability

/-!
# GameTheory.Concepts.WelfareTheorems

Welfare theorems relating social welfare to individual expected utilities.

## Main results

- `IsTeamGame.socialWelfare_eq` — in a team game with `n` players,
  social welfare equals `n * eu σ i` for any player `i`
- `socialWelfare_nonneg_of_nonneg_eu` — if all players have non-negative EU,
  social welfare is non-negative
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

set_option linter.unusedFintypeInType false in
/-- In a team game, social welfare equals `card ι * eu σ i` for any player `i`,
    since all players share the same expected utility. -/
theorem IsTeamGame.socialWelfare_eq [Fintype ι] [Inhabited ι]
    {G : KernelGame ι} (hteam : G.IsTeamGame) (σ : Profile G) (i : ι) :
    G.socialWelfare σ = Fintype.card ι * G.eu σ i := by
  simp only [KernelGame.socialWelfare]
  have heu : ∀ j : ι, G.eu σ j = G.eu σ i := by
    intro j
    rw [KernelGame.eu, KernelGame.eu]
    congr with ω
    exact hteam ω j i
  calc
    ∑ j : ι, G.eu σ j = ∑ _j : ι, G.eu σ i := by
      apply Finset.sum_congr rfl
      intro j _
      exact heu j
    _ = Fintype.card ι * G.eu σ i := by
      simp [Finset.sum_const, nsmul_eq_mul]

set_option linter.unusedFintypeInType false in
/-- If all players have non-negative expected utility, social welfare is non-negative. -/
theorem socialWelfare_nonneg_of_nonneg_eu [Fintype ι]
    {G : KernelGame ι} {σ : Profile G}
    (h : ∀ i, G.eu σ i ≥ 0) : G.socialWelfare σ ≥ 0 :=
  Finset.sum_nonneg (fun i _ => h i)

end KernelGame

end GameTheory
