/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.GameMorphism
import GameTheory.Concepts.ZeroSum.Minimax

/-!
# Minimax Concepts under Game Isomorphism

The library's two-player saddle-point predicate is equivalent to Nash
equilibrium for every game, so its transport is an immediate Nash corollary.
-/

namespace GameTheory
namespace KernelGame
namespace EUGameIsomorphism

variable {G H : KernelGame (Fin 2)}

/-- Saddle points are invariant under expected-utility game isomorphism. -/
theorem isSaddlePoint_iff (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsSaddlePoint σ ↔ H.IsSaddlePoint (e.profileEquiv σ) :=
  (isSaddlePoint_iff_isNash G σ).trans <|
    (e.nash_iff σ).trans (isSaddlePoint_iff_isNash H _).symm

end EUGameIsomorphism
end KernelGame
end GameTheory
