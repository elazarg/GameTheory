import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! Oriented edge and triangle flux for three-color Sperner labelings.
Only transitions between colors zero and one contribute to the flux. The
triangle flux detects exactly the triangles containing all three colors. -/

namespace GameTheory.Math.Sperner

/-- Signed flux along an edge, counting transitions between colors zero and one. -/
def edgeFlux (a b : Fin 3) : ℤ :=
  if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then -1 else 0

/-- Sum of the signed edge fluxes around an oriented triangle. -/
def triangleFlux (a b c : Fin 3) : ℤ := edgeFlux a b + edgeFlux b c + edgeFlux c a

/-- A triangle is trichromatic when its three vertex colors are pairwise distinct. -/
def Trichromatic (a b c : Fin 3) : Prop := a ≠ b ∧ b ≠ c ∧ c ≠ a

/-- Trichromaticity of three finite colors is computably decidable. -/
instance (a b c : Fin 3) : Decidable (Trichromatic a b c) :=
  inferInstanceAs (Decidable (a ≠ b ∧ b ≠ c ∧ c ≠ a))

/-- A monochromatic edge has zero flux. -/
@[simp] theorem edgeFlux_self (a : Fin 3) : edgeFlux a a = 0 := by
  fin_cases a <;> decide

/-- Reversing an edge reverses its signed flux. -/
theorem edgeFlux_reverse (a b : Fin 3) : edgeFlux b a = -edgeFlux a b := by
  fin_cases a <;> fin_cases b <;> decide

/-- On a two-color boundary, edge flux is the change in the color-one indicator. -/
theorem edgeFlux_eq_indicator_sub {a b : Fin 3} (ha : a ≠ 2) (hb : b ≠ 2) :
    edgeFlux a b = (if b = 1 then (1 : ℤ) else 0) - (if a = 1 then (1 : ℤ) else 0) := by
  fin_cases a <;> fin_cases b <;> simp_all [edgeFlux]

/-- Edges whose endpoints both avoid color zero have no flux. -/
theorem edgeFlux_eq_zero_of_ne_zero {a b : Fin 3} (ha : a ≠ 0) (hb : b ≠ 0) :
    edgeFlux a b = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all [edgeFlux]

/-- Edges whose endpoints both avoid color one have no flux. -/
theorem edgeFlux_eq_zero_of_ne_one {a b : Fin 3} (ha : a ≠ 1) (hb : b ≠ 1) :
    edgeFlux a b = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all [edgeFlux]

/-- Triangle flux is nonzero exactly when all three colors occur. -/
theorem triangleFlux_ne_zero_iff_trichromatic (a b c : Fin 3) :
    triangleFlux a b c ≠ 0 ↔ Trichromatic a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

/-- A triangle missing a color contributes no net flux. -/
theorem triangleFlux_eq_zero_of_not_trichromatic (a b c : Fin 3)
    (h : ¬Trichromatic a b c) : triangleFlux a b c = 0 := by
  by_cases hz : triangleFlux a b c = 0
  · exact hz
  · exact False.elim (h ((triangleFlux_ne_zero_iff_trichromatic a b c).mp hz))

/-- A trichromatic triangle has unit flux, with its sign determined by orientation. -/
theorem triangleFlux_eq_one_or_neg_one_iff_trichromatic (a b c : Fin 3) :
    (triangleFlux a b c = 1 ∨ triangleFlux a b c = -1) ↔ Trichromatic a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

end GameTheory.Math.Sperner
