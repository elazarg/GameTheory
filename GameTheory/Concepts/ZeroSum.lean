/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.ConstantSum

/-!
# Zero-Sum Games

Theorems about zero-sum kernel games, specialized from the constant-sum
results with constant `0`. Since `IsZeroSum` is definitionally `IsConstantSum 0`,
each lemma below just instantiates the corresponding constant-sum lemma.

- `IsZeroSum.socialWelfare_eq_zero` — total expected utility is zero
- `IsZeroSum.eu_neg` — in a 2-player zero-sum game, one player's EU is the negation of the other's
-/

namespace GameTheory

open Math.Probability
namespace KernelGame

variable {ι : Type}

/-- In a zero-sum game with finite players and per-player bounded utility, the
    social welfare is zero. -/
theorem IsZeroSum.socialWelfare_eq_zero_of_bounded [Fintype ι] {G : KernelGame ι}
    (hzs : G.IsZeroSum) (σ : Profile G)
    {C : ι → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) : G.socialWelfare σ = 0 :=
  hzs.socialWelfare_eq_of_bounded σ hbd

/-- In a zero-sum game with finite outcomes and finite players,
    the social welfare (sum of all players' expected utilities) is always zero. -/
theorem IsZeroSum.socialWelfare_eq_zero [Fintype ι] {G : KernelGame ι} [Finite G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) : G.socialWelfare σ = 0 :=
  hzs.socialWelfare_eq σ

/-- In a 2-player zero-sum game with bounded utility, one player's EU is the
    negation of the other's. -/
theorem IsZeroSum.eu_neg_of_bounded {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) (σ : Profile G)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.eu σ 0 = - G.eu σ 1 := by
  have h := hzs.eu_determined_of_bounded σ hbd
  linarith

/-- In a 2-player zero-sum game with finite outcomes,
    one player's expected utility is the negation of the other's. -/
theorem IsZeroSum.eu_neg {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) (σ : Profile G) :
    G.eu σ 0 = - G.eu σ 1 := by
  have h := hzs.eu_determined σ
  linarith

end KernelGame
end GameTheory
