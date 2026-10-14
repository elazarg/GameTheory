module

public import GameTheory.Math.Probability.Uniform
public import GameTheory.Math.Probability.Support
public import GameTheory.Math.Probability.Joint
public import Mathlib.Logic.Equiv.Fin.Basic
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

/-! Uniform laws survive bijections and forgetting independent coordinates.
Finite tuple projections apply to every finite alphabet, including empty tuples.
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {α β : Type*}

/-- A bijection transports the finite uniform law to the finite uniform law. -/
theorem uniformOfFintype_map_equiv [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) :
    (uniformLaw α).map e = uniformLaw β := by
  ext b
  obtain ⟨a, rfl⟩ := e.surjective b
  rw [pmf_map_apply_of_injective _ e.injective]
  simp only [uniformLaw_apply, Fintype.card_congr e]

/-- A uniform product is the joint law of two independent uniform draws. -/
theorem uniformOfFintype_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    uniformLaw (α × β) =
      bindPairLaw (uniformLaw α) (fun _ => uniformLaw β) := by
  ext ⟨a, b⟩
  rw [bindPairLaw_apply]
  simp only [uniformLaw_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv] <;> simp

/-- The first coordinate of a uniform product is uniform. -/
theorem uniformOfFintype_map_fst [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (uniformLaw (α × β)).map Prod.fst = uniformLaw α := by
  rw [uniformOfFintype_prod, bindPairLaw_map_fst]

/-- The second coordinate of a uniform product is uniform. -/
theorem uniformOfFintype_map_snd [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    (uniformLaw (α × β)).map Prod.snd = uniformLaw β := by
  rw [uniformOfFintype_prod, bindPairLaw_map_snd, PMF.bind_const]

/-- Restricting a uniform finite tuple to its prefix preserves uniformity. -/
theorem uniformOfFintype_map_fin_prefix [Fintype α] [Nonempty α] (s t : ℕ) :
    (uniformLaw (Fin (s + t) → α)).map
      (fun choices => fun i : Fin s => choices ⟨i.val, by omega⟩) =
      uniformLaw (Fin s → α) := by
  rw [← uniformOfFintype_map_equiv (Fin.appendEquiv s t), PMF.map_comp]
  have h : (fun choices : Fin (s + t) → α => fun i : Fin s => choices ⟨i.val, by omega⟩) ∘
      (Fin.appendEquiv s t) = Prod.fst := by
    funext p i
    change Fin.append p.1 p.2 (Fin.castAdd t i) = p.1 i
    exact Fin.append_left _ _ _
  rw [h, uniformOfFintype_map_fst]

/-- Restricting a uniform finite tuple to its suffix preserves uniformity. -/
theorem uniformOfFintype_map_fin_suffix [Fintype α] [Nonempty α] (s t : ℕ) :
    (uniformLaw (Fin (s + t) → α)).map
      (fun choices => fun i : Fin s => choices ⟨i.val + t, by omega⟩) =
      uniformLaw (Fin s → α) := by
  let e : (Fin t → α) × (Fin s → α) ≃ (Fin (s + t) → α) :=
    (Fin.appendEquiv t s).trans (Equiv.arrowCongr
      (finCongr (Nat.add_comm t s)) (Equiv.refl α))
  rw [← uniformOfFintype_map_equiv e, PMF.map_comp]
  have h : (fun choices : Fin (s + t) → α =>
      fun i : Fin s => choices ⟨i.val + t, by omega⟩) ∘ e = Prod.snd := by
    funext p i
    change Fin.append p.1 p.2 ⟨i.val + t, by omega⟩ = p.2 i
    have hindex : (⟨i.val + t, by omega⟩ : Fin (t + s)) = Fin.natAdd t i := by
      ext
      simp [Nat.add_comm]
    rw [hindex, Fin.append_right]
  rw [h, uniformOfFintype_map_snd]

end GameTheory.Math.Probability
