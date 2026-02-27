import GameTheory.MAID
import GameTheory.MAID_EFG

/-!
# MAID Example

A minimal MAID: one player, one decision node, one utility node.
Player 0 picks action 0 or 1. Utility rewards action 0 with payoff 1, action 1 with payoff 0.

Demonstrates:
- Concrete `Struct` and `Sem` construction
- `toKernelGame` bridge
- `maidToEFG_udist` preservation theorem
-/

namespace MAID

open GameTheory

/-! ## Structure -/

/-- A tiny MAID: 2 nodes, 1 player.
    - Node 0: decision for player 0 (binary choice)
    - Node 1: utility for player 0 (observes node 0's choice) -/
def tinyStruct : Struct (Fin 1) 2 where
  kind := fun | 0 => .decision 0 | 1 => .utility 0
  parents := fun | 0 => ∅ | 1 => {0}
  obsParents := fun | 0 => ∅ | 1 => {0}
  domainSize := fun | 0 => 2 | 1 => 1
  topoOrder := [0, 1]
  obs_sub := fun nd => by fin_cases nd <;> simp
  obs_eq_nondec := fun nd h => by
    fin_cases nd
    · exact absurd ⟨0, rfl⟩ h
    · rfl
  utility_domain := fun nd _a h => by
    fin_cases nd <;> simp_all
  nonutility_pos := fun nd h => by
    fin_cases nd
    · exact Nat.zero_lt_succ _
    · exact absurd ⟨0, rfl⟩ h
  topo_nodup := by decide
  topo_length := by decide
  topo_acyclic := by decide

/-! ## Semantics -/

/-- Semantics for the tiny MAID: no chance nodes, utility = 1 for action 0, 0 for action 1. -/
noncomputable def tinySem : Sem tinyStruct where
  chanceCPD := fun ⟨nd, hnd⟩ => by
    exfalso; fin_cases nd <;> simp [tinyStruct] at hnd
  utilityFn := fun _p ⟨nd, hnd⟩ cfg =>
    match nd, hnd with
    | ⟨0, _⟩, hnd => absurd hnd (by simp [tinyStruct])
    | ⟨1, _⟩, _ =>
      if (cfg ⟨(0 : Fin 2), by simp [tinyStruct]⟩).val = 0 then 1 else 0

/-! ## Policy -/

/-- Policy that always picks action 0. -/
noncomputable def tinyPol0 : Policy tinyStruct :=
  fun _p _I => PMF.pure ⟨0, tinyStruct.dom_pos _⟩

/-! ## KernelGame bridge and udist -/

/-- The MAID KernelGame for our tiny example. -/
noncomputable def tinyKG : KernelGame (Fin 1) :=
  toKernelGame tinyStruct tinySem

/-- The MAID → EFG reduction preserves `udist` (applying the general theorem). -/
noncomputable example :
    (MAID_EFG.maidToEFG tinyStruct tinySem tinyPol0).toKernelGame.udist
      (MAID_EFG.toEFGProfile tinyPol0) =
    tinyKG.udist tinyPol0 :=
  MAID_EFG.maidToEFG_udist tinySem tinyPol0

end MAID
