import GameTheory.Finite.BimatrixTable
import GameTheory.Core.BimatrixGame
import Mathlib.Tactic.Linarith

/-! The executable tally decoder recovers every bounded payoff cell of an
encoded table. Decoded tables compile to the canonical symmetric bimatrix game. -/

noncomputable section

namespace GameTheory.Finite.BimatrixTable

/-- Reading the unary header recovers its exact dimension. -/
theorem decodeDimension_encodeTable (q : ℕ) (A : ℕ → ℕ → ℤ) :
    decodeDimension (encodeTable q A) = q := by
  simp [decodeDimension, encodeTable]

/-- Bounded integer cells occupy exactly two fixed-width tally blocks. -/
theorem encodeEntry_length (q : ℕ) (z : ℤ) (hz : z.natAbs ≤ q + 2) :
    (encodeEntry q z).length = 2 * (q + 2) := by
  have h := Int.toNat_add_toNat_neg_eq_natAbs z
  simp only [encodeEntry, List.length_append, List.length_replicate]
  omega

private theorem length_flatMap_fixed {α β : Type*} (xs : List α) (f : α → List β)
    (w : ℕ) (hf : ∀ a ∈ xs, (f a).length = w) :
    (xs.flatMap f).length = xs.length * w := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hf a (by simp)
    have ht : ∀ b ∈ xs, (f b).length = w := fun b hb => hf b (by simp [hb])
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ha, ih ht]
    simp [Nat.add_mul, Nat.add_comm]

private theorem block_flatMap_fixed {α β : Type*} (xs : List α) (f : α → List β)
    (w : ℕ) (hf : ∀ a ∈ xs, (f a).length = w) (k : ℕ) (hk : k < xs.length) :
    ((xs.flatMap f).drop (k * w)).take w = f xs[k] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons a xs ih =>
    have ha := hf a (by simp)
    have ht : ∀ b ∈ xs, (f b).length = w := fun b hb => hf b (by simp [hb])
    cases k with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, List.flatMap_cons, List.getElem_cons_zero]
      rw [← ha, List.take_append_length]
    | succ k =>
      have hk' : k < xs.length := by simpa using hk
      simp only [List.flatMap_cons, Nat.succ_mul, List.getElem_cons_succ]
      rw [Nat.add_comm, ← ha, List.drop_length_add_append]
      simpa only [ha] using ih ht k hk'

/-- The exact output length is cubic in the unary table dimension. -/
theorem encodeTable_length (q : ℕ) (A : ℕ → ℕ → ℤ)
    (hbound : ∀ i < q, ∀ j < q, (A i j).natAbs ≤ q + 2) :
    (encodeTable q A).length = q + 1 + q * q * (2 * (q + 2)) := by
  have hr (i : ℕ) (hi : i ∈ List.range q) :
      ((List.range q).flatMap (fun j => encodeEntry q (A i j))).length = q * (2 * (q + 2)) := by
    simpa only [List.length_range] using length_flatMap_fixed (List.range q)
      (fun j => encodeEntry q (A i j)) (2 * (q + 2))
      (fun j hj => encodeEntry_length q (A i j) (hbound i (List.mem_range.mp hi) j (List.mem_range.mp hj)))
  have hb := length_flatMap_fixed (List.range q)
    (fun i => (List.range q).flatMap (fun j => encodeEntry q (A i j)))
    (q * (2 * (q + 2))) hr
  simp only [encodeTable, List.length_append, List.length_replicate, List.length_cons,
    hb, List.length_range]
  simp [Nat.mul_assoc, Nat.add_assoc, Nat.add_comm]

private theorem encoded_cell (q : ℕ) (A : ℕ → ℕ → ℤ)
    (hbound : ∀ i < q, ∀ j < q, (A i j).natAbs ≤ q + 2)
    (i j : ℕ) (hi : i < q) (hj : j < q) :
    (((List.range q).flatMap (fun r => (List.range q).flatMap (fun c => encodeEntry q (A r c)))).drop
      ((i * q + j) * (2 * (q + 2)))).take (2 * (q + 2)) = encodeEntry q (A i j) := by
  let w := 2 * (q + 2)
  let rows := fun r => (List.range q).flatMap (fun c => encodeEntry q (A r c))
  have hlen (r : ℕ) (hr : r ∈ List.range q) : (rows r).length = q * w := by
    simpa only [List.length_range] using length_flatMap_fixed (List.range q)
      (fun c => encodeEntry q (A r c)) w
      (fun c hc => encodeEntry_length q (A r c) (hbound r (List.mem_range.mp hr) c (List.mem_range.mp hc)))
  have hrow : (((List.range q).flatMap rows).drop (i * (q * w))).take (q * w) = rows i := by
    have h := block_flatMap_fixed (List.range q) rows (q * w) hlen i (by simpa using hi)
    rw [List.getElem_range] at h
    exact h
  have hcell : ((rows i).drop (j * w)).take w = encodeEntry q (A i j) := by
    have h :=
      block_flatMap_fixed (List.range q) (fun c => encodeEntry q (A i c)) w
        (fun c hc => encodeEntry_length q (A i c) (hbound i hi c (List.mem_range.mp hc)))
        j (by simpa using hj)
    rw [List.getElem_range] at h
    exact h
  change (((List.range q).flatMap rows).drop ((i * q + j) * w)).take w = _
  have hfit : w ≤ q * w - j * w := by
    have h := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at h
    omega
  have hs : (((List.range q).flatMap rows).drop ((i * q + j) * w)).take w =
      (((((List.range q).flatMap rows).drop (i * (q * w))).take (q * w)).drop (j * w)).take w := by
    rw [List.drop_take, List.take_take, Nat.min_eq_left hfit, List.drop_drop]
    simp only [Nat.add_mul, Nat.mul_assoc]
  rw [hs, hrow, hcell]

private theorem entry_tallies (q : ℕ) (z : ℤ) (hz : z.natAbs ≤ q + 2) :
    (((encodeEntry q z).take (q + 2)).count true : ℤ) -
      (((encodeEntry q z).drop (q + 2)).count true : ℤ) = z := by
  let pos := List.replicate z.toNat true ++ List.replicate (q + 2 - z.toNat) false
  let neg := List.replicate (-z).toNat true ++ List.replicate (q + 2 - (-z).toNat) false
  have h := Int.toNat_add_toNat_neg_eq_natAbs z
  have hp : pos.length = q + 2 := by
    simp only [pos, List.length_append, List.length_replicate]
    omega
  change (((pos ++ neg).take (q + 2)).count true : ℤ) -
    (((pos ++ neg).drop (q + 2)).count true : ℤ) = z
  rw [← hp, List.take_append_length, List.drop_append_length]
  simp only [pos, neg, List.count_append, List.count_replicate]
  simp

/-- The actual decoder recovers every in-range cell of a bounded encoded table. -/
theorem decode_encoded_table (q : ℕ) (A : ℕ → ℕ → ℤ)
    (hbound : ∀ i < q, ∀ j < q, (A i j).natAbs ≤ q + 2)
    (i j : ℕ) (hi : i < q) (hj : j < q) :
    decodedPayoff (encodeTable q A) i j = A i j := by
  have hpayload : (encodeTable q A).drop (q + 1) =
      (List.range q).flatMap (fun r => (List.range q).flatMap (fun c => encodeEntry q (A r c))) := by
    simp [encodeTable, List.drop_append]
  simp only [decodedPayoff, decodeDimension_encodeTable, hpayload,
    encoded_cell q A hbound i j hi hj]
  exact entry_tallies q (A i j) (hbound i hi j hj)

/-- A decoded word denotes the existing canonical symmetric bimatrix game. -/
@[reducible] def decodedGame (input : List Bool) : UtilityGame (Fin 2) :=
  let q := decodeDimension input
  MatrixGame.bimatrixGame
    (fun i j : Fin q => (decodedPayoff input i j : ℝ))
    (fun i j : Fin q => (decodedPayoff input j i : ℝ))

/-- Decoding the bounded serialization reproduces the original canonical game,
including its action carrier and both payoff functions. -/
theorem decodedGame_encodeTable (q : ℕ) (A : ℕ → ℕ → ℤ)
    (hbound : ∀ i < q, ∀ j < q, (A i j).natAbs ≤ q + 2) :
    decodedGame (encodeTable q A) =
      MatrixGame.bimatrixGame (fun i j : Fin q => (A i j : ℝ))
        (fun i j : Fin q => (A j i : ℝ)) := by
  unfold decodedGame
  rw [decodeDimension_encodeTable]
  dsimp only
  congr 1 <;> funext i j
  · exact congrArg (fun z : ℤ => (z : ℝ)) (decode_encoded_table q A hbound i j i.isLt j.isLt)
  · exact congrArg (fun z : ℤ => (z : ℝ)) (decode_encoded_table q A hbound j i j.isLt i.isLt)

end GameTheory.Finite.BimatrixTable
