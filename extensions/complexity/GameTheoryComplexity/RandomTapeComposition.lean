import GameTheoryComplexity.RandomTape
import GameTheory.Math.Probability.Support
import Mathlib.Logic.Equiv.Fin.Basic

/-! Ignoring unused fair random bits preserves the full verdict law. -/

noncomputable section

namespace GameTheory.Complexity

open GameTheory.Math.Probability

private theorem uniform_map_equiv {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext b
  obtain ⟨a, rfl⟩ := e.surjective b
  rw [pmf_map_apply_of_injective _ e.injective]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]

private theorem uniform_map_fst {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.fst = PMF.uniformOfFintype α := by
  classical
  ext a
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp [PMF.uniformOfFintype_apply, Fintype.card_prod]
  have hβ : (Fintype.card β : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.mul_inv, ← mul_assoc, mul_comm (Fintype.card β : ENNReal), mul_assoc,
    ENNReal.mul_inv_cancel hβ (by simp), mul_one] <;> simp

private theorem uniform_map_snd {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype (α × β)).map Prod.snd = PMF.uniformOfFintype β := by
  rw [← uniform_map_equiv (Equiv.prodComm β α), PMF.map_comp]
  exact uniform_map_fst

/-- A suffix of a uniform fair tape is itself a uniform fair tape. -/
theorem randomTapeLaw_suffix (s t : ℕ) (verdict : (Fin s → Bool) → Bool) :
    randomTapeLaw (s + t)
      (fun choices => verdict (fun i => choices ⟨i.val + t, by omega⟩)) =
      randomTapeLaw s verdict := by
  let e : (Fin t → Bool) × (Fin s → Bool) ≃ (Fin (s + t) → Bool) :=
    (Fin.appendEquiv t s).trans (Equiv.arrowCongr
      (finCongr (Nat.add_comm t s)) (Equiv.refl Bool))
  rw [randomTapeLaw, ← uniform_map_equiv e, PMF.map_comp]
  have h : (fun choices : Fin (s + t) → Bool =>
      verdict (fun i => choices ⟨i.val + t, by omega⟩)) ∘ e =
      verdict ∘ Prod.snd := by
    funext p
    apply congrArg verdict
    funext i
    change Fin.append p.1 p.2 ⟨i.val + t, by omega⟩ = p.2 i
    have hindex : (⟨i.val + t, by omega⟩ : Fin (t + s)) = Fin.natAdd t i := by
      ext
      simp [Nat.add_comm]
    rw [hindex, Fin.append_right]
  rw [h, ← PMF.map_comp, uniform_map_snd]
  rfl

/-- A prefix of a uniform fair tape is itself a uniform fair tape. -/
theorem randomTapeLaw_prefix (s t : ℕ) (verdict : (Fin s → Bool) → Bool) :
    randomTapeLaw (s + t)
      (fun choices => verdict (fun i => choices ⟨i.val, by omega⟩)) =
      randomTapeLaw s verdict := by
  rw [randomTapeLaw, ← uniform_map_equiv (Fin.appendEquiv s t), PMF.map_comp]
  have h : (fun choices : Fin (s + t) → Bool => verdict (fun i => choices ⟨i.val, by omega⟩)) ∘
      (Fin.appendEquiv s t) = verdict ∘ Prod.fst := by
    funext p
    apply congrArg verdict
    funext i
    change Fin.append p.1 p.2 (Fin.castAdd t i) = p.1 i
    exact Fin.append_left _ _ _
  rw [h, ← PMF.map_comp, uniform_map_fst]
  rfl

end GameTheory.Complexity
