import GameTheory.Math.Probability.Joint
import GameTheory.Math.Probability.Product

noncomputable section

open GameTheory.Math.Probability

namespace GameTheory.Tests.PMFProductAlgebra

theorem snd_consumer (μ : PMF (Fin 2)) (ν : PMF Bool) :
    (bindPairLaw μ (fun _ => ν)).map Prod.snd = ν := by
  rw [bindPairLaw_map_snd]
  simp

theorem pure_right_consumer (μ : PMF (Fin 2)) (b : Bool) :
    bindPairLaw μ (fun _ => PMF.pure b) = μ.map (fun a => (a, b)) := by
  rw [bindPairLaw]
  have hkernel : (fun a : Fin 2 =>
      PMF.map (fun value : Bool => (a, value)) (PMF.pure b)) =
    PMF.pure ∘ fun a => (a, b) := by
    funext a
    rw [PMF.pure_map]
    rfl
  rw [hkernel, PMF.bind_pure_comp]

theorem assoc_consumer (μ : PMF (Fin 2)) (ν : PMF Bool)
    (ξ : PMF (Fin 3)) :
    (bindPairLaw (bindPairLaw μ (fun _ => ν)) (fun _ => ξ)).map
      (fun p => (p.1.1, (p.1.2, p.2))) =
        bindPairLaw μ (fun _ => bindPairLaw ν (fun _ => ξ)) := by
  ext target
  rcases target with ⟨a, b, c⟩
  rw [PMF.map_apply]
  rw [tsum_eq_single ((a, b), c)]
  · rw [bindPairLaw_apply, bindPairLaw_apply]
    simp [bindPairLaw_apply, mul_assoc]
  · intro other hne
    rcases other with ⟨ab, c'⟩
    rcases ab with ⟨a', b'⟩
    have hne' : (a, (b, c)) ≠ (a', (b', c')) := by
      intro h
      exact hne (by cases h; rfl)
    simp [hne']

end GameTheory.Tests.PMFProductAlgebra
