/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.CoalitionalGame.Additive
import GameTheory.Cooperative.GaleShapley.Strategyproofness

/-!
# GameTheory.Cooperative.Tests

Compilation validation entrypoint for cooperative-game modules.
-/

namespace GameTheory.Cooperative.Tests

noncomputable section

example (α : Fin 3 → ℝ) (i : Fin 3) :
    (CoalGame.additiveGame α).shapleyValue i = α i :=
  CoalGame.additiveGame_shapleyValue α i

example (i : Fin 3) : CoalGame.majorityGame3.shapleyValue i = 1 / 3 :=
  CoalGame.majorityGame3_shapleyValue i

namespace MatchingMarket

variable {α β : Type} [Fintype α] [Fintype β]
variable {M M' : MatchingMarket α β}

example (a : α)
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hAinj' : ∀ a, Function.Injective (M'.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b)
    (hreport : M.IsUnilateralProposerReport M' a) :
    ¬M.StrictlyImprovesOnDA M'.daMatching a :=
  M.deferredAcceptance_strategyproof a hAinj hAinj' hBinj hAne hreport

example
    (hAinj : ∀ a, Function.Injective (M.prefA a))
    (hAinj' : ∀ a, Function.Injective (M'.prefA a))
    (hBinj : ∀ b, Function.Injective (M.prefB b))
    (hAne : ∀ a b, M.reserveA a ≠ M.prefA a b)
    (hreport : M.IsProposerReport M')
    (hchanged : M.prefA ≠ M'.prefA) :
    ∃ a, M.prefA a ≠ M'.prefA a ∧
      ¬M.StrictlyImprovesOnDA M'.daMatching a :=
  M.deferredAcceptance_groupStrategyproof hAinj hAinj' hBinj
    hAne hreport hchanged

end MatchingMarket

end

end GameTheory.Cooperative.Tests
