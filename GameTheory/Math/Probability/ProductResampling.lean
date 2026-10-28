module

/-
# Resampling one independent coordinate

Drawing one coordinate afresh from its marginal law preserves a finite
independent product. The unused original coordinate is integrated out, so no
finiteness or support bound on the coordinate carrier is needed.
-/

public import GameTheory.Math.Probability.Product

@[expose] public section

noncomputable section

namespace GameTheory.Math.Probability

/-- Resampling one coordinate independently preserves the product law. -/
theorem independentProduct_resample {ι A : Type*} [Fintype ι] [DecidableEq ι]
    (laws : ι → PMF A) (j : ι) :
    independentProduct laws =
      (laws j).bind (fun value => (independentProduct laws).map
        (fun s i => if i = j then value else s i)) := by
  have hm (value : A) :
      (independentProduct laws).map (fun s i => if i = j then value else s i) =
        (independentProduct (fun i : {i // i ≠ j} => laws i)).map
          (fun rest => (Equiv.piSplitAt j (fun _ => A)).symm (value, rest)) := by
    rw [independentProduct_splitAt laws j, PMF.map_bind]
    have hf (old : A) :
        (fun s i => if i = j then value else s i) ∘
            (fun rest => (Equiv.piSplitAt j (fun _ => A)).symm (old, rest)) =
          (fun rest => (Equiv.piSplitAt j (fun _ => A)).symm (value, rest)) := by
      funext rest i
      by_cases hi : i = j
      · subst i
        simp [Equiv.piSplitAt_symm_apply]
      · simp [Equiv.piSplitAt_symm_apply, hi]
    simp_rw [PMF.map_comp, hf]
    exact PMF.bind_const _ _
  simp_rw [hm]
  exact independentProduct_splitAt laws j

end GameTheory.Math.Probability
