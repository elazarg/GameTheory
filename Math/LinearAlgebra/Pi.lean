/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Linear Algebra on Function Spaces

Project-local generic lemmas for linear equivalences between coordinate
function spaces.
-/

namespace Math
namespace LinearAlgebra

/-- Relabeling the coordinates of a family of vectors by an equivalence
preserves and reflects linear independence. -/
theorem linearIndependent_piCongrLeft_iff
    {Y S R I : Type*} [Ring R] {v : I → Y → R} (e : Y ≃ S) :
    LinearIndependent R (fun i =>
      LinearEquiv.piCongrLeft R (fun _ : S => R) e (v i)) ↔
      LinearIndependent R v := by
  let E : (Y → R) ≃ₗ[R] (S → R) :=
    LinearEquiv.piCongrLeft R (fun _ : S => R) e
  constructor
  · intro h
    change LinearIndependent R (E.toLinearMap ∘ v) at h
    exact LinearIndependent.of_comp E.toLinearMap h
  · intro h
    change LinearIndependent R (E.toLinearMap ∘ v)
    exact h.map' E.toLinearMap E.ker

end LinearAlgebra
end Math
