module

public import GameTheoryComplexity.Sperner

@[expose] public section

/-! Succinct Sperner controls cover zero coordinate width, malformed color
circuits, canonical source exclusion, binary coordinates, and native encoded verification. -/

namespace GameTheory.Complexity.Tests.Sperner

open GameTheory.Complexity.Backend GameTheory.Math.Sperner
open Turing.MultiTapeTM
open Cslib.Complexity

private def smallestGrid : List Bool := CircuitWords.encodePair [] []
private def twoByTwoGrid : List Bool := CircuitWords.encodePair [false] []

example : spernerVerdict smallestGrid [true, false] = true ∧
    spernerVerdict smallestGrid [true, true] = false ∧
    spernerVerdict smallestGrid [false, false] = false ∧
    spernerVerdict smallestGrid [false, true] = false := by decide

example : spernerVerdict smallestGrid [] = false ∧
    spernerVerdict smallestGrid [true] = false ∧
    spernerVerdict smallestGrid [true, false, false] = false := by decide

example : spernerVerdict twoByTwoGrid (encodeGridNode 1 (some ⟨1, 0, true⟩)) = true ∧
    spernerVerdict twoByTwoGrid (encodeGridNode 1 none) = false := by decide

example : spernerVerdict (CircuitWords.encodePair [] [false]) [true, false] = true ∧
    spernerVerdict (CircuitWords.encodePair [true] [false, true])
      (encodeGridNode 1 (some ⟨1, 0, true⟩)) = true := by decide

example : spernerRelation smallestGrid [true, false] :=
  (spernerVerdict_accept _ _).mp (by decide)

example : ¬spernerRelation smallestGrid [true, true] := by
  intro h
  have hv := (spernerVerdict_accept _ _).mpr h
  have hf : spernerVerdict smallestGrid [true, true] = false := by decide
  rw [hf] at hv
  cases hv

example : ComputableInPolyTime (fun p : List Bool × List Bool => spernerVerdict p.1 p.2)
    (encPair encBits encBits) encBool :=
  spernerVerdict_polyTime (ComputableInPolyTime.fst encBits encBits)
    (ComputableInPolyTime.snd encBits encBits)

private theorem nativeMembership : spernerRelation ∈ Cslib.Complexity.PPAD encBits :=
  GameTheory.Complexity.spernerRelation_mem_PPAD

example : spernerRelation ∈ Cslib.Complexity.TFNP encBits :=
  PPAD_subset_TFNP nativeMembership

example (input : List Bool) : ∃ word, spernerRelation input word :=
  (PPAD_subset_TFNP nativeMembership).2 input

example : SearchReducible encBits encBits spernerRelation endOfLineRelation :=
  exists_spernerToEndOfLineReduction

example : ∃ f : List Bool → List Bool, ComputableInPolyTime f encBits encBits ∧
    endOfLineWidth (f (CircuitWords.encodePair [true] [false, true])) = 4 := by
  obtain ⟨f, hf, heval⟩ := exists_spernerEndOfLineInstance
  refine ⟨f, hf, ?_⟩
  simpa only [CircuitWords.first_encodePair, List.length_singleton, gridNodeWidth] using
    (heval (CircuitWords.encodePair [true] [false, true])).1

example : SearchComplete @PPAD encBits spernerRelation :=
  GameTheory.Complexity.spernerRelation_PPADComplete

example : SearchReducible encBits encBits endOfLineRelation spernerRelation :=
  exists_endOfLineToSpernerReduction

end GameTheory.Complexity.Tests.Sperner
