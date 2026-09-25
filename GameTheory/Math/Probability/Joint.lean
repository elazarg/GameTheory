import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Joint laws of a draw and its conditional continuation -/

noncomputable section

namespace GameTheory.Math.Probability

/-- Draw from `p`, then from `q`, retaining both coordinates. -/
def bindPairLaw {α β : Type*} (p : PMF α)
    (q : α → PMF β) : PMF (α × β) :=
  p.bind fun a => (q a).map fun b => (a, b)

/-- Atom masses in a joint draw factor into outer and conditional masses. -/
theorem bindPairLaw_apply {α β : Type*} (p : PMF α)
    (q : α → PMF β) (a : α) (b : β) :
    bindPairLaw p q (a, b) = p a * q a b := by
  rw [bindPairLaw, PMF.bind_apply]
  have hmap (x : α) : (PMF.map (fun y => (x, y)) (q x)) (x, b) = q x b := by
    rw [PMF.map_apply]
    rw [tsum_eq_single b]
    · simp
    · intro y hy
      have hne : (x, b) ≠ (x, y) := by
        intro heq
        exact hy (congrArg Prod.snd heq).symm
      simp [hne]
  rw [tsum_eq_single a]
  · rw [hmap a]
  · intro x hxa
    have hzero : (PMF.map (fun y => (x, y)) (q x)) (a, b) = 0 := by
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr
      intro y
      by_cases h : (a, b) = (x, y)
      · exact False.elim (hxa (congrArg Prod.fst h).symm)
      · simp [h]
    simp [hzero]

/-- Forgetting the first coordinate recovers the continuation mixture. -/
theorem bindPairLaw_map_snd {α β : Type*} (p : PMF α)
    (q : α → PMF β) :
    (bindPairLaw p q).map Prod.snd = p.bind q := by
  rw [bindPairLaw, PMF.map_bind]
  apply congrArg (fun k => p.bind k)
  funext a
  rw [PMF.map_comp]
  simpa only [Function.comp_def,
    show (fun x : β => x) = id from rfl] using (PMF.map_id (q a))

/-- Forgetting the continuation recovers the original draw. -/
theorem bindPairLaw_map_fst {α β : Type*} (p : PMF α)
    (q : α → PMF β) :
    (bindPairLaw p q).map Prod.fst = p := by
  rw [bindPairLaw, PMF.map_bind]
  calc
    p.bind (fun a => ((q a).map fun b => (a, b)).map Prod.fst) =
        p.bind PMF.pure := by
      apply congrArg (fun k => p.bind k)
      funext a
      rw [PMF.map_comp]
      rw [show Prod.fst ∘ (fun b : β => (a, b)) =
        Function.const β a from rfl, PMF.map_const]
    _ = p := PMF.bind_pure p

/-- The same atom factorization when the recorded coordinates are swapped. -/
theorem bindPairLaw_swap_apply {α β : Type*} (p : PMF α)
    (q : α → PMF β) (b : β) (a : α) :
    ((bindPairLaw p q).map Prod.swap) (b, a) = p a * q a b := by
  rw [PMF.map_apply, tsum_eq_single (a, b)]
  · simp [bindPairLaw_apply]
  · intro pair hpair
    have hne : (b, a) ≠ Prod.swap pair := by
      intro heq
      exact hpair (Prod.swap_injective (by simpa using heq.symm))
    simp [hne]

end GameTheory.Math.Probability
