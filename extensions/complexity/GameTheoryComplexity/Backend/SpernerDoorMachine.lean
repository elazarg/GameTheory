import GameTheoryComplexity.Backend.EndOfLineMachineOps
import GameTheory.Math.SpernerDoors

/-! Constant-size word controls select oriented zero/one doors. The selection
order agrees with the mathematical door function; no triangle enumeration is needed. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham EndOfLineMachineOps
open GameTheory.Math.Sperner

/-- Recognize the requested oriented zero/one edge on canonical color words. -/
def gridEdgeDoorFlag (incoming : Bool) (a b : List Bool) : List Bool :=
  andBit (eqFlag a (if incoming then [false, false] else [true, false]))
    (eqFlag b (if incoming then [true, false] else [false, false]))

/-- Select the first present door, or retain the original vertex. -/
def gridChooseDoor (incoming : Bool) (a b c r₀ r₁ r₂ stay : List Bool) : List Bool :=
  caseBit₀ (gridEdgeDoorFlag incoming a b) r₀
    (caseBit₀ (gridEdgeDoorFlag incoming b c) r₁
      (caseBit₀ (gridEdgeDoorFlag incoming c a) r₂ stay))

/-- Oriented edge recognition composes polynomial-time color producers. -/
theorem gridEdgeDoorFlagFn_mem_FP (incoming : Bool) {a b : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => gridEdgeDoorFlag incoming (a z) (b z)) ∈ FP :=
  andBitFn_mem_FP (eqFlagFn_mem_FP ha (constFn_mem_FP _))
    (eqFlagFn_mem_FP hb (constFn_mem_FP _))

/-- Door selection composes polynomial-time controls and neighbor producers. -/
theorem gridChooseDoorFn_mem_FP (incoming : Bool)
    {a b c r₀ r₁ r₂ stay : List Bool → List Bool}
    (ha : a ∈ FP) (hb : b ∈ FP) (hc : c ∈ FP)
    (h₀ : r₀ ∈ FP) (h₁ : r₁ ∈ FP) (h₂ : r₂ ∈ FP) (hs : stay ∈ FP) :
    (fun z => gridChooseDoor incoming (a z) (b z) (c z)
      (r₀ z) (r₁ z) (r₂ z) (stay z)) ∈ FP :=
  selectFn_mem_FP (gridEdgeDoorFlagFn_mem_FP incoming ha hb) h₀
    (selectFn_mem_FP (gridEdgeDoorFlagFn_mem_FP incoming hb hc) h₁
      (selectFn_mem_FP (gridEdgeDoorFlagFn_mem_FP incoming hc ha) h₂ hs))

/-- Canonical color controls select exactly the mathematical door. -/
theorem gridChooseDoor_colors (incoming : Bool) (a b c : Fin 3)
    (r₀ r₁ r₂ stay : List Bool) :
    gridChooseDoor incoming [decide (a = 1), decide (a = 2)]
      [decide (b = 1), decide (b = 2)] [decide (c = 1), decide (c = 2)]
      r₀ r₁ r₂ stay =
      match door a b c incoming with
      | none => stay
      | some p => if p = 0 then r₀ else if p = 1 then r₁ else r₂ := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> cases incoming <;> rfl

end GameTheory.Complexity.Backend
