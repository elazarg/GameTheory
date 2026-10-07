import Complexitylib.Classes.FNP.Defs
import Complexitylib.Classes.P

/-! Polynomial search reductions preserve every target solution and retain the
original instance when decoding. Search totality and efficient verification are
separate properties: a reduction transports the former, not the latter. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity
open _root_.Complexity.Cobham

/-- An efficient instance map and solution decoder preserving every valid target
solution. The decoder receives the source instance as its first argument. -/
structure SearchReduction (R T : List Bool → List Bool → Prop) where
  /-- Compute the target instance from the original source instance. -/
  instanceMap : List Bool → List Bool
  instanceMap_mem_FP : instanceMap ∈ FP
  /-- Decode a target solution using both the source instance and that solution. -/
  decode : (Fin 2 → List Bool) → List Bool
  decode_mem_FPn : FPn decode
  sound : ∀ x y, T (instanceMap x) y → R x (decode ![x, y])

namespace SearchReduction

variable {R T U : List Bool → List Bool → Prop}

/-- Identity maps leave both instances and solutions unchanged. -/
def refl (R : List Bool → List Bool → Prop) : SearchReduction R R where
  instanceMap := id
  instanceMap_mem_FP := id_mem_FP
  decode := fun v => v 1
  decode_mem_FPn := cobham_iff_FPn.mp (.proj 1)
  sound := fun _ _ h => h

/-- Compose instance maps forward and solution decoders backward. Each decoder
receives the instance belonging to its own reduction. -/
def trans (a : SearchReduction R T) (b : SearchReduction T U) : SearchReduction R U where
  instanceMap := b.instanceMap ∘ a.instanceMap
  instanceMap_mem_FP := mem_FP_comp a.instanceMap_mem_FP b.instanceMap_mem_FP
  decode := fun v => a.decode ![v 0, b.decode ![a.instanceMap (v 0), v 1]]
  decode_mem_FPn := by
    have hm : Cobham (fun v : Fin 2 → List Bool => a.instanceMap (v 0)) :=
      Cobham.comp (FP_subset_CobhamFP a.instanceMap_mem_FP) fun _ => .proj 0
    exact cobham_iff_FPn.mp
      (Cobham.comp₂ (cobham_iff_FPn.mpr a.decode_mem_FPn) (.proj 0)
        (Cobham.comp₂ (cobham_iff_FPn.mpr b.decode_mem_FPn) hm (.proj 1)))
  sound := by
    intro x y hy
    exact a.sound x _ (b.sound (a.instanceMap x) y hy)

/-- A total target supplies a valid source solution for every input word. -/
theorem total (a : SearchReduction R T) (hT : ∀ x, ∃ y, T x y) :
    ∀ x, ∃ y, R x y := by
  intro x
  obtain ⟨y, hy⟩ := hT (a.instanceMap x)
  exact ⟨a.decode ![x, y], a.sound x y hy⟩

/-- Verification and balance of the source relation must be supplied separately:
solution preservation alone imposes no bound on its other accepted witnesses. -/
theorem mem_TFNP (a : SearchReduction R T) (hR : R ∈ FNP) (hT : T ∈ TFNP) :
    R ∈ TFNP :=
  ⟨hR, a.total hT.2⟩

end SearchReduction
end GameTheory.Complexity.Backend
