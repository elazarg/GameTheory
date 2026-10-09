import GameTheory.Finite.BimatrixPathBinaryCodec

/-! Canonical source encoding, strict feasibility and malformed node controls. -/
namespace GameTheory.Tests.BimatrixPathBinaryCodec
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

private def A : Fin 1 → Fin 1 → ℤ := fun _ _ => 1
private def B : Fin 1 → Fin 1 → ℤ := fun _ _ => 2
private def origin : BimatrixPathPort A B 0 := bimatrixSourcePort A B 0

example : encode origin = [false, false, false, false, false, false, false, false] := by
  decide +kernel

example : decode A B 0 (encode origin) = some origin := decode_encode origin

example : membershipWord (bimatrixSlackVariables 1 1) = [true, false, true, false] := by
  decide +kernel

example : ((membershipWord (bimatrixSlackVariables 1 1)).take
    (index (m := 1) (n := 1) (toLex ((1 : Fin 2), false))).val).count true = 1 := by decide +kernel

example : toLex ((1 : Fin 2), false) =
    (bimatrixSlackVariables 1 1).orderEmbOfFin bimatrixSlackVariables_card 1 := by
  apply (selected_variable_iff (m := 1) (n := 1) _ bimatrixSlackVariables_card 1 _).mpr
  exact ⟨by decide +kernel, by decide +kernel⟩

-- Short words, missing basis columns, and two entering variables are rejected.
example : (decode A B 0 []).isNone = true := by decide +kernel

example : (decode A B 0
    [true, false, false, false, false, false, false, false]).isNone = true := by
  decide +kernel

example : (decode A B 0
    [false, false, false, false, true, false, false, false]).isNone = true := by
  decide +kernel

-- An invertible matrix with a negative symbolic constant fails feasibility.
example : ¬ IntegerFeasible (k := 1)
    (fun _ _ => (-1 : ℤ)) := by
  intro h
  have hs : GameTheory.Math.FiniteLexicographicCompare.lexLT (fun _ => (0 : ℤ))
      (GameTheory.Math.IntegerDictionaryComputation.coefficients
        (fun _ : Fin 1 => fun _ : Fin 1 => (-1 : ℤ)) (fun _ => 1) 0) = false := by
    decide +kernel
  have ht := h.2 (0 : Fin 1)
  rw [hs] at ht
  cases ht

example (f : BimatrixPathPort A B 0 → BimatrixPathPort A B 0) :
    transport f [] = [] := by
  apply transport_invalid
  rfl

-- Semantic transport cannot turn any malformed encoding into a raw endpoint.
example (P S : BimatrixPathPort A B 0 → BimatrixPathPort A B 0) :
    ¬ GameTheory.Math.EndOfLine.RawWitness (transport P) (transport S) (encode origin) [] := by
  apply not_rawWitness_of_invalid
  rfl

end GameTheory.Tests.BimatrixPathBinaryCodec
