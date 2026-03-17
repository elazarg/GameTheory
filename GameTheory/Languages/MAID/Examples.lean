import GameTheory.Languages.MAID.Syntax

/-!
# MAID Examples

Reader-facing MAID examples demonstrating concrete diagrams and their native
semantic objects. Compilation/SOS validation belongs in
`GameTheory.Languages.MAID.Tests`.
-/

namespace MAID

open GameTheory

/-! ## Structure -/

/-- Parent relation for the tiny MAID. -/
private def tinyParents : Fin 2 → Finset (Fin 2) := fun | 0 => ∅ | 1 => {0}

private theorem tinyParents_acyclic : DAG.Acyclic (· ∈ tinyParents ·) := by
  intro nd hnd
  -- On Fin 2 with parents 1 → {0} and 0 → ∅, the only edge is 0 → 1.
  -- TransGen can only go 0 → 1, never back.
  have h01 : ∀ a b : Fin 2, a ∈ tinyParents b → a = 0 ∧ b = 1 := by
    intro a b hab; fin_cases b
    · exact absurd hab (Finset.notMem_empty _)
    · exact ⟨Finset.mem_singleton.mp hab, rfl⟩
  -- Any TransGen step reaches 1, so further steps fail (nothing in tinyParents 0)
  have : ∀ a b : Fin 2, Relation.TransGen (· ∈ tinyParents ·) a b → a = 0 ∧ b = 1 := by
    intro a b hab
    induction hab with
    | single h => exact h01 _ _ h
    | tail _ hbc ih =>
      obtain ⟨_, rfl⟩ := h01 _ _ hbc
      exact ⟨ih.1, rfl⟩
  obtain ⟨rfl, h⟩ := this nd nd hnd
  exact absurd h (by decide)

/-- A tiny MAID: 2 nodes, 1 player.
    - Node 0: decision for player 0 (binary choice)
    - Node 1: utility for player 0 (observes node 0's choice) -/
def tinyStruct : Struct (Fin 1) 2 where
  kind := fun | 0 => .decision 0 | 1 => .utility 0
  parents := tinyParents
  obsParents := tinyParents
  Val := fun | 0 => Fin 2 | 1 => Unit
  instFintype := fun | 0 => inferInstance | 1 => inferInstance
  instDecidableEq := fun | 0 => inferInstance | 1 => inferInstance
  instInhabited := fun | 0 => inferInstance | 1 => inferInstance
  obs_sub := fun _ => Finset.Subset.refl _
  obs_eq_nondec := fun nd h => by
    fin_cases nd
    · exact absurd ⟨0, rfl⟩ h
    · rfl
  utility_unique := fun
    | 0, _, h => absurd h nofun
    | 1, _, _ => ⟨⟨()⟩, fun _ => rfl⟩
  acyclic := tinyParents_acyclic

/-! ## Semantics -/

/-- Semantics for the tiny MAID: no chance nodes, utility = 1 for action 0, 0
for action 1. -/
noncomputable def tinySem : Sem tinyStruct where
  chanceCPD := fun ⟨nd, hnd⟩ => by
    exfalso; fin_cases nd <;> simp [tinyStruct] at hnd
  utilityFn := fun _p ⟨nd, hnd⟩ cfg =>
    match nd, hnd with
    | ⟨0, _⟩, hnd => absurd hnd (by simp [tinyStruct])
    | ⟨1, _⟩, _ =>
      if (cfg ⟨(0 : Fin 2), by simp [tinyStruct, tinyParents]⟩) = (0 : Fin 2) then 1 else 0

/-! ## Policy -/

/-- Policy that always picks action 0. -/
noncomputable def tinyPol0 : Policy tinyStruct :=
  fun _p _I => PMF.pure default

/-! ## Topological order -/

/-- The canonical topological order for the tiny MAID. -/
def tinyOrder : TopologicalOrder tinyStruct where
  order := [0, 1]
  nodup := by decide
  length := by decide
  respects := by
    intro i p hp
    fin_cases i <;> simp_all [tinyStruct, tinyParents]

/-! ## KernelGame bridge -/

/-- The MAID KernelGame for our tiny example. -/
noncomputable def tinyKG : KernelGame (Fin 1) :=
  toKernelGame tinyStruct tinySem

/-- The tiny MAID induces a well-formed outcome distribution on total assignments. -/
noncomputable example : PMF (TAssign tinyStruct) :=
  evalAssignDist tinyStruct tinySem tinyPol0

end MAID
