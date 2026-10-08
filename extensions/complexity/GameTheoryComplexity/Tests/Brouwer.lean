import GameTheoryComplexity.Brouwer

/-! Rational-point controls include nonzero accepted residuals, malformed
lengths, out-of-square coordinates, diagonal choices, and the closed far edge. -/

namespace GameTheory.Complexity.Tests.Brouwer

open _root_.Complexity GameTheory.Complexity.Backend GameTheory.Math.Sperner
open GameTheory.Math.Brouwer

private def smallestGrid : List Bool := pair [] []

private theorem smallestGrid_relation_iff (p : ℕ × ℕ)
    (hx : p.1 ≤ 6) (hy : p.2 ≤ 6) :
    brouwerRelation smallestGrid (encodeBrouwerPoint 0 p) ↔
      |(sixthDisplacement (spernerColor smallestGrid) 1 p.1 p.2).1| ≤ 1 / 6 ∧
      |(sixthDisplacement (spernerColor smallestGrid) 1 p.1 p.2).2| ≤ 1 / 6 := by
  rw [brouwerRelation_local_iff]
  have hd : decodeBrouwerPoint 0 (encodeBrouwerPoint 0 p) = some p :=
    decodeBrouwerPoint_encode 0 p (by simpa using hx) (by simpa using hy)
  simp only [smallestGrid, pairFst_pair, List.length_nil, hd,
    Option.some.injEq, pow_zero]
  exact ⟨fun ⟨_, he, hr⟩ => he.symm ▸ hr, fun hr => ⟨p, rfl, hr⟩⟩

private theorem verdict_false_of_not_relation {input word : List Bool}
    (h : ¬brouwerRelation input word) : brouwerVerdict input word = [false] := by
  rcases brouwerVerdict_flag input word with ht | hf
  · exact False.elim (h ((brouwerVerdict_accept input word).mp ht))
  · exact hf

private theorem accepted_nonzero :
    brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (4, 1)) = [true] := by
  apply (brouwerVerdict_accept _ _).mpr
  rw [smallestGrid_relation_iff _ (by decide) (by decide)]
  norm_num [smallestGrid, sixthDisplacement, sixthTriangle, sixthWeights,
    sixthOffset, sixthCellIndex, spernerColor, standardGridColor, corner,
    weightedDisplacement, colorDisplacement]

private theorem accepted_barycenter :
    brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (4, 2)) = [true] := by
  apply (brouwerVerdict_accept _ _).mpr
  rw [smallestGrid_relation_iff _ (by decide) (by decide)]
  norm_num [smallestGrid, sixthDisplacement, sixthTriangle, sixthWeights,
    sixthOffset, sixthCellIndex, spernerColor, standardGridColor, corner,
    weightedDisplacement, colorDisplacement]

private theorem rejected_large :
    brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (5, 1)) = [false] := by
  apply verdict_false_of_not_relation
  rw [smallestGrid_relation_iff _ (by decide) (by decide)]
  norm_num [smallestGrid, sixthDisplacement, sixthTriangle, sixthWeights,
    sixthOffset, sixthCellIndex, spernerColor, standardGridColor, corner,
    weightedDisplacement, colorDisplacement]

example : brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (4, 1)) = [true] ∧
    brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (4, 2)) = [true] ∧
    brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (5, 1)) = [false] :=
  ⟨accepted_nonzero, accepted_barycenter, rejected_large⟩

example : brouwerVerdict smallestGrid [] = [false] ∧
    brouwerVerdict smallestGrid [true] = [false] ∧
    brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (7, 1)) = [false] ∧
    brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (1, 7)) = [false] := by decide

example : brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (6, 6)) = [false] ∧
    brouwerVerdict smallestGrid (encodeBrouwerPoint 0 (0, 0)) = [false] := by
  constructor <;> apply verdict_false_of_not_relation <;>
    rw [smallestGrid_relation_iff _ (by decide) (by decide)] <;>
    norm_num [smallestGrid, sixthDisplacement, sixthTriangle, sixthWeights,
      sixthOffset, sixthCellIndex, spernerColor, standardGridColor, corner,
      weightedDisplacement, colorDisplacement]

example : brouwerLocate smallestGrid (encodeBrouwerPoint 0 (6, 6)) =
    encodeGridNode 0 (some ⟨0, 0, false⟩) ∧
    brouwerLocate (pair [false] []) (encodeBrouwerPoint 1 (7, 7)) =
      encodeGridNode 1 (some ⟨1, 1, false⟩) := by decide

example : brouwerPairedVerdict (pair smallestGrid (encodeBrouwerPoint 0 (4, 1))) =
    [true] ∧ brouwerPairedVerdict [] = [false] ∧
    brouwerPairedVerdict [false] = [false] := by
  constructor
  · apply (brouwerPairedVerdict_accept _).mpr
    exact ⟨smallestGrid, encodeBrouwerPoint 0 (4, 1), rfl,
      (brouwerVerdict_accept _ _).mp accepted_nonzero⟩
  · constructor <;> decide

example : brouwerRelation smallestGrid (encodeBrouwerPoint 0 (4, 1)) :=
  (brouwerVerdict_accept _ _).mp accepted_nonzero

example : ¬brouwerRelation smallestGrid (encodeBrouwerPoint 0 (5, 1)) := by
  intro h
  have ht := (brouwerVerdict_accept _ _).mpr h
  rw [rejected_large] at ht
  cases ht

end GameTheory.Complexity.Tests.Brouwer
