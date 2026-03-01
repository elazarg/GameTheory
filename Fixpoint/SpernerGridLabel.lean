import Fixpoint.GridSimplex
import Fixpoint.SpernerLabeling

set_option autoImplicit false

namespace Fixpoint

section GridLabel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Label for a grid vertex, induced by the Sperner-style simplex label. -/
noncomputable def gridLabel
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    {m : ℕ} (hm : 0 < m) (p : GridPoint ι m) : ι :=
  spernerLabel f (GridPoint.toStdSimplex (ι := ι) hm p)

/-- Boundary admissibility on grid vertices: if coordinate `i` is zero, label is not `i`. -/
theorem gridLabel_ne_of_coord_eq_zero
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    {m : ℕ} (hm : 0 < m) (p : GridPoint ι m) (i : ι)
    (hpi : p.1 i = 0) :
    gridLabel f hm p ≠ i := by
  have hcoord0 : (GridPoint.toStdSimplex (ι := ι) hm p : ι → ℝ) i = 0 := by
    simp [GridPoint.toStdSimplex_apply, hpi]
  simpa [gridLabel] using
    (spernerLabel_ne_of_coord_eq_zero
      (f := f)
      (x := GridPoint.toStdSimplex (ι := ι) hm p)
      (i := i)
      hcoord0)

end GridLabel

end Fixpoint
