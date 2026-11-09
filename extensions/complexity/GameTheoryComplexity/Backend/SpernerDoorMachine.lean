module

public import GameTheoryComplexity.Backend.WordOperations
public import GameTheory.Math.SpernerDoors

@[expose] public section

/-! Constant-size word controls select oriented zero/one doors. The selection
order agrees with the mathematical door function; no triangle enumeration is needed. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM
open ComputableInPolyTime
open WordOperations
open GameTheory.Math.Sperner

/-- Recognize the requested oriented zero/one edge on canonical color words. -/
def gridEdgeDoorFlag (incoming : Bool) (a b : List Bool) : List Bool :=
  andFlag (eqFlag a (if incoming then [false, false] else [true, false]))
    (eqFlag b (if incoming then [true, false] else [false, false]))

/-- Select the first present door, or retain the original vertex. -/
def gridChooseDoor (incoming : Bool) (a b c r₀ r₁ r₂ stay : List Bool) : List Bool :=
  select (gridEdgeDoorFlag incoming a b) r₀
    (select (gridEdgeDoorFlag incoming b c) r₁
      (select (gridEdgeDoorFlag incoming c a) r₂ stay))

/-- Oriented edge recognition charges both color producers. -/
@[fun_prop] theorem gridEdgeDoorFlag_polyTime (incoming : Bool)
    {α : Type} {enc : α ↪ List Bool} {a b : α → List Bool}
    (ha : ComputableInPolyTime a enc encBits) (hb : ComputableInPolyTime b enc encBits) :
    ComputableInPolyTime (fun x => gridEdgeDoorFlag incoming (a x) (b x)) enc encBits :=
  andFlag_polyTime.comp
    ((eqFlag_polyTime.comp (ha.prod (const _))).prod
      (eqFlag_polyTime.comp (hb.prod (const _))))

/-- Door selection charges every color and neighbor producer. -/
@[fun_prop] theorem gridChooseDoor_polyTime (incoming : Bool)
    {α : Type} {enc : α ↪ List Bool} {a b c r₀ r₁ r₂ stay : α → List Bool}
    (ha : ComputableInPolyTime a enc encBits) (hb : ComputableInPolyTime b enc encBits)
    (hc : ComputableInPolyTime c enc encBits) (h₀ : ComputableInPolyTime r₀ enc encBits)
    (h₁ : ComputableInPolyTime r₁ enc encBits) (h₂ : ComputableInPolyTime r₂ enc encBits)
    (hs : ComputableInPolyTime stay enc encBits) :
    ComputableInPolyTime (fun x => gridChooseDoor incoming (a x) (b x) (c x)
      (r₀ x) (r₁ x) (r₂ x) (stay x)) enc encBits :=
  select_polyTime.comp ((gridEdgeDoorFlag_polyTime incoming ha hb).prod
    (h₀.prod (select_polyTime.comp ((gridEdgeDoorFlag_polyTime incoming hb hc).prod
      (h₁.prod (select_polyTime.comp ((gridEdgeDoorFlag_polyTime incoming hc ha).prod
        (h₂.prod hs))))))))

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
