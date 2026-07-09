/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Cooperative.CoalitionalGame.Additive

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

end

end GameTheory.Cooperative.Tests
