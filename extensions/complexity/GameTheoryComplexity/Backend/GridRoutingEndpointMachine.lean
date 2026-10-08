import GameTheoryComplexity.Backend.GridRoutingCodecMachine
import GameTheoryComplexity.Backend.GridRoutingDivision
import GameTheory.Math.GridWire

/-! An original routed vertex has vertical coordinate six times its label.
Binary division followed by a fixed-width low-bit extraction recovers that label
in polynomial time, independently of the coordinate's numeric magnitude. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham GameTheory.Math.GridWire

/-- Recover a `b`-bit vertex label from the routing word's vertical coordinate. -/
def routingEndpointLabelBits (ruler word : List Bool) : List Bool :=
  (routingDivSixBits (routingPointYBits ruler word)).take ruler.length

private theorem fromBitsLE_take_of_lt (width : ℕ) (bits : List Bool)
    (h : Nat.fromBitsLE bits < 2 ^ width) :
    Nat.fromBitsLE (bits.take width) = Nat.fromBitsLE bits := by
  induction width generalizing bits with
  | zero =>
    change 0 = Nat.fromBitsLE bits
    simp only [pow_zero] at h
    omega
  | succ width ih =>
    cases bits with
    | nil => rfl
    | cons bit bits =>
      have ht : Nat.fromBitsLE bits < 2 ^ width := by
        rw [Nat.fromBitsLE_cons, pow_succ] at h
        cases bit <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h <;> omega
      simp only [List.take_succ_cons, Nat.fromBitsLE_cons, ih bits ht]

/-- An accepted routing word yields exactly the original vertex label width. -/
theorem routingEndpointLabelBits_length {ruler word : List Bool}
    (hw : word.length = routingPointWidth ruler.length) :
    (routingEndpointLabelBits ruler word).length = ruler.length := by
  simp only [routingEndpointLabelBits, List.length_take, routingDivSixBits_length,
    routingPointYBits, List.length_drop, hw, routingPointWidth, routingCoordinateWidth]
  omega

/-- Decoding an original vertex recovers its bounded label as a natural number. -/
theorem routingEndpointLabelBits_value {ruler word : List Bool} {i : ℕ}
    (hd : decodeRoutingPoint ruler.length word = some (vertexPoint i))
    (hi : i < 2 ^ ruler.length) : Nat.fromBitsLE (routingEndpointLabelBits ruler word) = i := by
  have hw := decodeRoutingPoint_length hd
  have hy : Nat.fromBitsLE (routingPointYBits ruler word) = 6 * i := by
    unfold decodeRoutingPoint at hd
    rw [ite_eq_left hw] at hd
    have h := congrArg Prod.snd (Option.some.inj hd)
    exact h
  have hq : Nat.fromBitsLE (routingDivSixBits (routingPointYBits ruler word)) = i := by
    rw [routingDivSixBits_value, hy]
    simp
  unfold routingEndpointLabelBits
  rw [fromBitsLE_take_of_lt ruler.length _ (by rw [hq]; exact hi), hq]

/-- The recovered label word is the canonical little-endian encoding of the vertex. -/
theorem routingEndpointLabelBits_eq_bits {ruler word : List Bool} {i : ℕ}
    (hd : decodeRoutingPoint ruler.length word = some (vertexPoint i))
    (hi : i < 2 ^ ruler.length) :
    routingEndpointLabelBits ruler word = Nat.toBitsLE ruler.length i := by
  have h := Nat.toBitsLE_fromBitsLE (routingEndpointLabelBits ruler word)
  rw [routingEndpointLabelBits_length (decodeRoutingPoint_length hd),
    routingEndpointLabelBits_value hd hi] at h
  exact h.symm

/-- Label extraction composes actual polynomial-time word producers uniformly. -/
theorem routingEndpointLabelBitsFn_mem_FP {ruler word : List Bool → List Bool}
    (hr : ruler ∈ FP) (hw : word ∈ FP) :
    (fun z => routingEndpointLabelBits (ruler z) (word z)) ∈ FP := by
  have hdiv := mem_FP_comp (routingPointYBitsFn_mem_FP hr hw) routingDivSixBits_mem_FP
  apply CobhamFP_subset_FP
  exact takeFn (FP_subset_CobhamFP hr) (FP_subset_CobhamFP hdiv)

end GameTheory.Complexity.Backend
