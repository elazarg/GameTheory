/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Transport.SolutionConcepts

/-!
# GameTheory.Concepts.Transport.Tests

Compilation checks for solution-concept transport APIs.
-/

namespace GameTheory.KernelGame.EUGameIsomorphism.Tests

noncomputable section

variable {ι : Type} [DecidableEq ι]
variable {G H : KernelGame ι}

example (e : EUGameIsomorphism G H) (ε : ℝ) (σ : Profile G) :
    G.IsεNash ε σ ↔ H.IsεNash ε (e.profileEquiv σ) :=
  e.isεNash_iff ε σ

example (e : EUGameIsomorphism G H) (σ τ : Profile G) :
    G.ParetoDominates σ τ ↔
      H.ParetoDominates (e.profileEquiv σ) (e.profileEquiv τ) :=
  e.paretoDominates_iff σ τ

example (e : EUGameIsomorphism G H) (Φ : Profile G → ℝ) :
    G.IsExactPotential Φ ↔ H.IsExactPotential (e.profileFunctionEquiv Φ) :=
  e.isExactPotential_iff Φ

example [Fintype ι] (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.socialWelfare σ = H.socialWelfare (e.profileEquiv σ) :=
  e.socialWelfare_eq σ

example {G H : KernelGame (Fin 2)} (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsSaddlePoint σ ↔ H.IsSaddlePoint (e.profileEquiv σ) :=
  e.isSaddlePoint_iff σ

end

end GameTheory.KernelGame.EUGameIsomorphism.Tests
