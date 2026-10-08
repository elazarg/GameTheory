import GameTheory.Math.GridSperner
import Mathlib.Tactic.IntervalCases

/-! Concrete grid controls cover both triangle orientations, arbitrary interior
colors, multiple boundary transitions, and failure without the boundary rules. -/

namespace GameTheory.Tests.GridSperner

open GameTheory.Math.Sperner
open scoped BigOperators

example : Trichromatic (standardGridColor 2 (fun _ _ => 2) 0 0)
    (standardGridColor 2 (fun _ _ => 2) 1 0)
    (standardGridColor 2 (fun _ _ => 2) 1 1) := by decide

example : Trichromatic (standardGridColor 2 (fun _ _ => 0) 1 0)
    (standardGridColor 2 (fun _ _ => 0) 2 1)
    (standardGridColor 2 (fun _ _ => 0) 1 1) := by decide

example (interior : ℕ → ℕ → Fin 3) :
    ∃ i < 2, ∃ j < 2,
      Trichromatic (standardGridColor 2 interior i j)
          (standardGridColor 2 interior (i + 1) j)
          (standardGridColor 2 interior (i + 1) (j + 1)) ∨
        Trichromatic (standardGridColor 2 interior i j)
          (standardGridColor 2 interior (i + 1) (j + 1))
          (standardGridColor 2 interior i (j + 1)) :=
  exists_grid_trichromatic (standardGridColor_boundary 2 interior (by decide))

example : ¬GridBoundary (fun _ _ => 0) 2 := by
  intro h
  exact h.2.2.1 0 (by omega) rfl

example (color : ℕ → ℕ → Fin 3) : ¬GridBoundary color 0 := by
  intro h
  obtain ⟨i, hi, _⟩ := exists_grid_trichromatic h
  omega

/-- The bottom boundary changes from zero to one, back to zero, then to one. -/
def alternatingBoundaryColor (i j : ℕ) : Fin 3 :=
  if j = 0 then if i = 4 then 1 else if i % 2 = 0 then 0 else 1
  else if i = 4 ∨ j = 4 then 2 else if i = 0 then 0 else 2

theorem alternatingBoundaryColor_valid : GridBoundary alternatingBoundaryColor 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro k hk; interval_cases k <;> decide

example : edgeFlux (alternatingBoundaryColor 0 0) (alternatingBoundaryColor 1 0) = 1 ∧
    edgeFlux (alternatingBoundaryColor 1 0) (alternatingBoundaryColor 2 0) = -1 ∧
    edgeFlux (alternatingBoundaryColor 2 0) (alternatingBoundaryColor 3 0) = 1 := by decide

example : (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
    (lowerFlux alternatingBoundaryColor i j + upperFlux alternatingBoundaryColor i j)) = 1 :=
  sum_gridFlux_eq_one alternatingBoundaryColor_valid

end GameTheory.Tests.GridSperner
