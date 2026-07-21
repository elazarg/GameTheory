/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.GameMorphism

/-!
# GameTheory.Concepts.Foundations.Tests

Compilation checks for game-isomorphism algebra and generic profile-function
transport.
-/

namespace GameTheory.KernelGame.EUGameIsomorphism.Tests

noncomputable section

variable {ι : Type} {G H K : KernelGame ι}

example (e : EUGameIsomorphism G H) (f : Profile G → ℕ) (σ : Profile G) :
    e.profileFunctionEquiv f (e.profileEquiv σ) = f σ := by
  simp

example (e : EUGameIsomorphism G H) : e.symm.symm = e := by
  simp

example (g : EUGameIsomorphism H K) (e : EUGameIsomorphism G H) :
    (EUGameIsomorphism.comp g e).profileEquiv =
      e.profileEquiv.trans g.profileEquiv :=
  profileEquiv_comp g e

example (g : EUGameIsomorphism H K) (e : EUGameIsomorphism G H) :
    EUGameIsomorphism.profileFunctionEquiv (α := ℕ) (EUGameIsomorphism.comp g e) =
      e.profileFunctionEquiv.trans g.profileFunctionEquiv :=
  profileFunctionEquiv_comp g e

end

end GameTheory.KernelGame.EUGameIsomorphism.Tests
