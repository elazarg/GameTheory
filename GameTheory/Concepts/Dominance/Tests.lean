/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Dominance.DominanceRelations

/-!
# Dominance Concept Tests

Compilation tests for dominance relation exports.
-/

namespace GameTheory.Concepts.Dominance.Tests

noncomputable section

def oneGame : KernelGame Bool :=
  KernelGame.ofPureEU (fun _ : Bool => PUnit) (fun _ _ => 0)

example (who : Bool) : oneGame.WeaklyDominates who PUnit.unit PUnit.unit :=
  KernelGame.WeaklyDominates.refl who PUnit.unit

example (who : Bool) :
    IsPreorder (oneGame.Strategy who) (oneGame.WeaklyDominates who) :=
  inferInstance

end

end GameTheory.Concepts.Dominance.Tests
