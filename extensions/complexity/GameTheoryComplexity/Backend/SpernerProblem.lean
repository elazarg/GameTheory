import GameTheoryComplexity.Backend.SpernerCornerMachine
import GameTheoryComplexity.Backend.CircuitVectorMachine

/-! Succinct square-grid Sperner instances consist of a coordinate-width ruler
and serialized color circuits. Boundary colors are enforced locally. Witnesses
are bounded triangle codes, rather than paths through the exponential grid. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity
open GameTheory.Math.Sperner

/-- The instance's locally boundary-corrected circuit coloring. -/
abbrev spernerColor (input : List Bool) : ℕ → ℕ → Fin 3 :=
  standardGridColor (2 ^ (pairFst input).length)
    (gridInteriorColor (pairFst input).length (evaluateCircuitVector (pairSnd input)))

/-- A decoded grid triangle with all three vertex colors distinct. -/
def spernerRelation (input word : List Bool) : Prop :=
  ∃ t, decodeGridNode (pairFst input).length word = some (some t) ∧
    Trichromatic
      (spernerColor input (corner t 0).1 (corner t 0).2)
      (spernerColor input (corner t 1).1 (corner t 1).2)
      (spernerColor input (corner t 2).1 (corner t 2).2)

/-- The two coordinate blocks and two tag bits have linear length in the instance. -/
theorem spernerRelation_polyBalanced : PolyBalanced spernerRelation := by
  refine ⟨Polynomial.X + Polynomial.X + 2, fun input word h => ?_⟩
  obtain ⟨t, hd, _⟩ := h
  have hw := decodeGridNode_length hd
  have hb := endOfLineWidth_le_length input
  change (pairFst input).length ≤ input.length at hb
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
  rw [hw, gridNodeWidth]
  omega

end GameTheory.Complexity.Backend
