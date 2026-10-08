import GameTheory.Math.SpernerTriangle

/-! Executable selection of oriented doors in a three-color triangle.
Each sign occurs on at most one edge. A triangle has exactly one unmatched
door precisely when its vertex colors are all distinct. -/

namespace GameTheory.Math.Sperner

/-- Flux on a numbered side of the oriented triangle: first, second, then closing edge. -/
def sideFlux (a b c : Fin 3) (p : Fin 3) : ℤ :=
  if p = 0 then edgeFlux a b else if p = 1 then edgeFlux b c else edgeFlux c a

/-- Select the unique door of the requested sign, checking the three sides in order. -/
def door (a b c : Fin 3) (incoming : Bool) : Option (Fin 3) :=
  let sign : ℤ := if incoming then 1 else -1
  if sideFlux a b c 0 = sign then some 0
  else if sideFlux a b c 1 = sign then some 1
  else if sideFlux a b c 2 = sign then some 2
  else none

/-- A side is selected exactly when its flux has the requested sign. -/
theorem door_eq_some_iff (a b c : Fin 3) (incoming : Bool) (p : Fin 3) :
    door a b c incoming = some p ↔
      sideFlux a b c p = (if incoming then (1 : ℤ) else -1) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> cases incoming <;> fin_cases p <;> decide

/-- A requested door is absent exactly when no side has the requested sign. -/
theorem door_eq_none_iff (a b c : Fin 3) (incoming : Bool) :
    door a b c incoming = none ↔
      ∀ p, sideFlux a b c p ≠ (if incoming then (1 : ℤ) else -1) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> cases incoming <;> decide

/-- Exactly one door orientation is present precisely for trichromatic triangles. -/
theorem door_imbalance_iff_trichromatic (a b c : Fin 3) :
    (door a b c true).isSome ≠ (door a b c false).isSome ↔ Trichromatic a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

end GameTheory.Math.Sperner
