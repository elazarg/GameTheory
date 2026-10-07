import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Int.Basic

/-! Executable binary serialization of a symmetric integer-payoff table.
The unary dimension header is followed by positive and negative tallies in
row-major order. Entries have the decoder's fixed width when their absolute
payoffs are at most the dimension plus two. -/

namespace GameTheory.Finite.BimatrixTable

/-- Two tally blocks, padded to the dimension plus two. Payoffs within that
bound have exactly this width; larger tallies are not truncated. -/
def encodeEntry (q : ℕ) (z : ℤ) : List Bool :=
  (List.replicate z.toNat true ++ List.replicate (q + 2 - z.toNat) false) ++
    (List.replicate (-z).toNat true ++ List.replicate (q + 2 - (-z).toNat) false)

/-- Unary dimension, delimiter, then the row-major payoff cells. -/
def encodeTable (q : ℕ) (A : ℕ → ℕ → ℤ) : List Bool :=
  List.replicate q true ++ false ::
    (List.range q).flatMap (fun i => (List.range q).flatMap (fun j => encodeEntry q (A i j)))

/-- The initial true tally determines the table dimension. -/
def decodeDimension (input : List Bool) : ℕ := (input.takeWhile id).length

/-- Read the signed tally at a row-major cell; malformed or missing blocks
are interpreted by the same total list operations. -/
def decodedPayoff (input : List Bool) (i j : ℕ) : ℤ :=
  let q := decodeDimension input
  let entry := ((input.drop (q + 1)).drop ((i * q + j) * (2 * (q + 2)))).take (2 * (q + 2))
  ((entry.take (q + 2)).count true : ℤ) - ((entry.drop (q + 2)).count true : ℤ)

end GameTheory.Finite.BimatrixTable
