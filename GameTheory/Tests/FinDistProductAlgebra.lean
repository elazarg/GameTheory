/-
# Finite-law product algebra regression

These consumers use three different finite carriers, so the product identities
are checked without relying on homogeneous or singleton carrier inference.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Tests.FinDistProductAlgebra

open GameTheory.Math.Probability

theorem snd_consumer (μ : FinDist (Fin 2)) (ν : FinDist Bool) :
    FinDist.map Prod.snd (FinDist.product μ ν) = ν := by
  exact FinDist.map_snd_product μ ν

theorem pure_right_consumer (μ : FinDist (Fin 2)) (b : Bool) :
    FinDist.product μ (FinDist.pure b) = FinDist.map (fun a => (a, b)) μ := by
  exact FinDist.product_pure_right μ b

theorem assoc_consumer (μ : FinDist (Fin 2)) (ν : FinDist Bool)
    (ξ : FinDist (Fin 3)) :
    FinDist.map (fun p : (Fin 2 × Bool) × Fin 3 =>
      (p.1.1, (p.1.2, p.2))) (FinDist.product (FinDist.product μ ν) ξ) =
        FinDist.product μ (FinDist.product ν ξ) := by
  exact FinDist.map_assoc_product μ ν ξ

end GameTheory.Tests.FinDistProductAlgebra
