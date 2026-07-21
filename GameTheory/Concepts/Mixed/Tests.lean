/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Mixed.GameMorphism

/-! Compilation tests for mixed-extension transport. -/

namespace GameTheory
namespace KernelGame

variable {ι : Type} [Fintype ι] {G H K : KernelGame ι}

open Classical in
example (e : GameIsomorphism G H) :
    (∃ σ : Profile G.mixedExtension, G.mixedExtension.IsNash σ) ↔
      ∃ τ : Profile H.mixedExtension, H.mixedExtension.IsNash τ :=
  e.mixedExtension_exists_isNash_iff

example (g : GameIsomorphism H K) (e : GameIsomorphism G H) :
    (GameIsomorphism.comp g e).mixedExtension =
      GameIsomorphism.comp g.mixedExtension e.mixedExtension :=
  GameIsomorphism.mixedExtension_comp g e

example (e : GameIsomorphism G H) :
    e.symm.mixedExtension = e.mixedExtension.symm :=
  GameIsomorphism.mixedExtension_symm e

end KernelGame
end GameTheory
