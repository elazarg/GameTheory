/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
import GameTheory.Experimental.PostArchitecture.PMFRestorationProbe
import GameTheory.Math.Probability.Product

open scoped BigOperators

namespace GameTheory.Experimental.PMFProductGate

open GameTheory.Math.Probability

private noncomputable def marginals : ∀ _i : Fin 2, PMF ℕ := fun i =>
  if i = 0 then PMFRestoration.geometric else PMF.pure 0

/-- A two-coordinate product with one genuinely infinite-support factor. -/
noncomputable def infiniteProduct : PMF (∀ _i : Fin 2, ℕ) :=
  independentProduct marginals

theorem firstMarginal :
    infiniteProduct.map (fun s => s 0) = PMFRestoration.geometric := by
  rw [infiniteProduct, independentProduct_map_eval]
  simp [marginals]

theorem support_infinite : infiniteProduct.support.Infinite := by
  intro hfinite
  have himage : (fun s : (∀ i : Fin 2, ℕ) => s 0) '' infiniteProduct.support |>.Finite :=
    hfinite.image _
  rw [← PMF.support_map, firstMarginal, PMFRestoration.geometric_support] at himage
  exact Set.infinite_univ himage

theorem no_finite_support_representation :
    ¬ ∃ law : PMF (∀ _i : Fin 2, ℕ),
      law.support.Finite ∧ law = infiniteProduct := by
  rintro ⟨law, hfinite, rfl⟩
  exact support_infinite hfinite

end GameTheory.Experimental.PMFProductGate
