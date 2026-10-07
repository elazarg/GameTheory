import GameTheoryComplexity.Sperner

/-! Succinct Sperner controls cover zero coordinate width, malformed color
circuits, canonical source exclusion, binary coordinates, and paired verification. -/

namespace GameTheory.Complexity.Tests.Sperner

open GameTheory.Complexity.Backend GameTheory.Math.Sperner
open _root_.Complexity

private def smallestGrid : List Bool := pair [] []
private def twoByTwoGrid : List Bool := pair [false] []

example : spernerVerdict smallestGrid [true, false] = [true] ∧
    spernerVerdict smallestGrid [true, true] = [false] ∧
    spernerVerdict smallestGrid [false, false] = [false] ∧
    spernerVerdict smallestGrid [false, true] = [false] := by decide

example : spernerVerdict smallestGrid [] = [false] ∧
    spernerVerdict smallestGrid [true] = [false] ∧
    spernerVerdict smallestGrid [true, false, false] = [false] := by decide

example : spernerVerdict twoByTwoGrid (encodeGridNode 1 (some ⟨1, 0, true⟩)) = [true] ∧
    spernerVerdict twoByTwoGrid (encodeGridNode 1 none) = [false] := by decide

example : spernerVerdict (pair [] [false]) [true, false] = [true] ∧
    spernerVerdict (pair [true] [false, true])
      (encodeGridNode 1 (some ⟨1, 0, true⟩)) = [true] := by decide

example : spernerPairedVerdict (pair smallestGrid [true, false]) = [true] ∧
    spernerPairedVerdict (pair smallestGrid [false, false]) = [false] ∧
    spernerPairedVerdict [] = [false] ∧ spernerPairedVerdict [false] = [false] := by decide

example : spernerRelation smallestGrid [true, false] :=
  (spernerVerdict_accept _ _).mp (by decide)

example : ¬spernerRelation smallestGrid [true, true] := by
  intro h
  have hv := (spernerVerdict_accept _ _).mpr h
  have hf : spernerVerdict smallestGrid [true, true] = [false] := by decide
  rw [hf] at hv
  cases hv

example : spernerPairedVerdict ∈ FP := spernerPairedVerdict_mem_FP

example : spernerRelation ∈ GameTheory.Complexity.PPAD :=
  GameTheory.Complexity.spernerRelation_mem_PPAD

example : spernerRelation ∈ TFNP := GameTheory.Complexity.spernerRelation_mem_TFNP

example (input : List Bool) : ∃ word, spernerRelation input word :=
  GameTheory.Complexity.spernerRelation_total input

example : Nonempty (SearchReduction spernerRelation endOfLineRelation) :=
  exists_spernerToEndOfLineReduction

example : ∃ f : List Bool → List Bool, f ∈ FP ∧
    endOfLineWidth (f (pair [true] [false, true])) = 4 := by
  obtain ⟨f, hf, heval⟩ := exists_spernerEndOfLineInstance
  refine ⟨f, hf, ?_⟩
  simpa only [pairFst_pair, List.length_singleton, gridNodeWidth] using
    (heval (pair [true] [false, true])).1

end GameTheory.Complexity.Tests.Sperner
