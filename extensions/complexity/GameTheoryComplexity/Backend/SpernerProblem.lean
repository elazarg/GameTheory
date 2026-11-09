module

public import GameTheoryComplexity.Backend.SpernerCornerMachine
public import GameTheoryComplexity.Backend.CircuitVectorMachine

@[expose] public section

/-! Succinct square-grid Sperner instances consist of a coordinate-width ruler
and serialized color circuits. Boundary colors are enforced locally. Witnesses
are bounded triangle codes, rather than paths through the exponential grid. -/

namespace GameTheory.Complexity.Backend

open GameTheory.Math.Sperner

/-- The instance's locally boundary-corrected circuit coloring. -/
abbrev spernerColor (input : List Bool) : ℕ → ℕ → Fin 3 :=
  standardGridColor (2 ^ (CircuitWords.first input).length)
    (gridInteriorColor (CircuitWords.first input).length (evaluateCircuitVector (CircuitWords.rest input)))

/-- A decoded grid triangle with all three vertex colors distinct. -/
def spernerRelation (input word : List Bool) : Prop :=
  ∃ t, decodeGridNode (CircuitWords.first input).length word = some (some t) ∧
    Trichromatic
      (spernerColor input (corner t 0).1 (corner t 0).2)
      (spernerColor input (corner t 1).1 (corner t 1).2)
      (spernerColor input (corner t 2).1 (corner t 2).2)

/-- The two coordinate blocks and two tag bits have linear length in the instance. -/
theorem spernerRelation_polyBalanced :
    ∃ p : Polynomial ℕ, ∀ input word, spernerRelation input word →
      word.length ≤ p.eval input.length := by
  refine ⟨Polynomial.X + Polynomial.X + 2, fun input word h => ?_⟩
  obtain ⟨t, hd, _⟩ := h
  have hw := decodeGridNode_length hd
  have hb := CircuitWords.first_length_le input
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
  rw [hw, gridNodeWidth]
  omega

end GameTheory.Complexity.Backend
