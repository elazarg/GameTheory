import GameTheory.Math.Probability.Joint

/-! Coordinatewise maps preserve the independent joint construction. -/

noncomputable section

namespace GameTheory.Math.Probability

/-- Mapping each independent coordinate maps their joint law coordinatewise. -/
theorem bindPairLaw_map {α β γ δ : Type*} (p : PMF α) (q : PMF β)
    (f : α → γ) (g : β → δ) :
    bindPairLaw (p.map f) (fun _ => q.map g) =
      (bindPairLaw p (fun _ => q)).map (fun x => (f x.1, g x.2)) := by
  rw [bindPairLaw, bindPairLaw, PMF.bind_map, PMF.map_bind]
  apply congrArg (PMF.bind p)
  funext a
  dsimp only [Function.comp_apply]
  rw [PMF.map_comp, PMF.map_comp]
  rfl

end GameTheory.Math.Probability
