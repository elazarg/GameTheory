import GameTheoryComplexity.Backend.BrouwerPointCodec
import GameTheoryComplexity.Backend.SpernerProblem
import GameTheory.Math.GridBrouwerSixthContinuous

/-! Approximate fixed-point search for succinct continuous unit-square maps.
Color circuits specify the vertex displacements of a globally continuous
triangular interpolant. Answers are arbitrary points on the advertised rational
output grid, with denominator six times the grid size; no triangle or barycenter
certificate is part of the answer. The tolerance measures the actual normalized
map residual, rather than distance to an exact fixed point. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity GameTheory.Math.Brouwer

/-- Rational-point approximate fixed points of the represented continuous map. -/
def brouwerRelation (input word : List Bool) : Prop :=
  ∃ p, decodeBrouwerPoint (pairFst input).length word = some p ∧
    SixthPointSmallResidual (spernerColor input) (2 ^ (pairFst input).length) p.1 p.2

/-- Exact local arithmetic evaluates the global normalized real-map residual. -/
theorem brouwerRelation_local_iff (input word : List Bool) :
    brouwerRelation input word ↔
      ∃ p, decodeBrouwerPoint (pairFst input).length word = some p ∧
        |(sixthDisplacement (spernerColor input) (2 ^ (pairFst input).length) p.1 p.2).1|
          ≤ 1 / 6 ∧
        |(sixthDisplacement (spernerColor input) (2 ^ (pairFst input).length) p.1 p.2).2|
          ≤ 1 / 6 := by
  constructor
  · rintro ⟨p, hd, hr⟩
    have hp := decodeBrouwerPoint_properties hd
    exact ⟨p, hd, (sixthPointSmallResidual_iff_local (spernerColor input)
      (Nat.two_pow_pos _) hp.2.1 hp.2.2.1).mp hr⟩
  · rintro ⟨p, hd, hr⟩
    have hp := decodeBrouwerPoint_properties hd
    exact ⟨p, hd, (sixthPointSmallResidual_iff_local (spernerColor input)
      (Nat.two_pow_pos _) hp.2.1 hp.2.2.1).mpr hr⟩

/-- Two numerator blocks have linear length in the serialized instance. -/
theorem brouwerRelation_polyBalanced : PolyBalanced brouwerRelation := by
  refine ⟨Polynomial.X + Polynomial.X + 6, fun input word h => ?_⟩
  obtain ⟨p, hd, _⟩ := h
  have hw := (decodeBrouwerPoint_properties hd).1
  have hb := endOfLineWidth_le_length input
  change (pairFst input).length ≤ input.length at hb
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
  rw [hw, pointWordWidth, pointCoordinateWidth]
  omega

end GameTheory.Complexity.Backend
