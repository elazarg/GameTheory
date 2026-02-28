import GameTheory.TeamGame
import GameTheory.ConstantSum

/-!
# GameTheory.WelfareTheorems

Welfare theorems relating social welfare to individual expected utilities.

## Main results

- `IsTeamGame.socialWelfare_eq` — in a team game with `n` players,
  social welfare equals `n * eu σ i` for any player `i`
- `socialWelfare_nonneg_of_nonneg_eu` — if all players have non-negative EU,
  social welfare is non-negative
-/

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

omit [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- In a team game, social welfare equals `card ι * eu σ i` for any player `i`,
    since all players share the same expected utility. -/
theorem IsTeamGame.socialWelfare_eq [Fintype ι] [Inhabited ι]
    {G : KernelGame ι} (hteam : G.IsTeamGame) (σ : Profile G) (i : ι) :
    G.socialWelfare σ = Fintype.card ι * G.eu σ i := by
  simp only [socialWelfare]
  conv_lhs => arg 2; ext j; rw [hteam.eu_eq σ j i]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq ι] in
set_option linter.unusedFintypeInType false in
/-- If all players have non-negative expected utility, social welfare is non-negative. -/
theorem socialWelfare_nonneg_of_nonneg_eu [Fintype ι]
    {G : KernelGame ι} {σ : Profile G}
    (h : ∀ i, G.eu σ i ≥ 0) : G.socialWelfare σ ≥ 0 :=
  Finset.sum_nonneg (fun i _ => h i)

end KernelGame

end GameTheory
