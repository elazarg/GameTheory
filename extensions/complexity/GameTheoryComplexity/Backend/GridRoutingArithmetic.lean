import GameTheoryComplexity.Backend.BinaryCertificateArithmetic

/-! Binary routing arithmetic reuses the exact adder and unsigned comparator.
The constant factors three and six use shifts and addition, with no numeric loops. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity _root_.Complexity.Cobham

/-- Add two little-endian words, retaining the full carry. -/
def routingAddBits (x y : List Bool) : List Bool := binaryCertificateAdd ![x, y]

/-- Compare arbitrary little-endian words as unsigned natural numbers. -/
def routingLEFlag (x y : List Bool) : List Bool := binaryCertificateLE ![x, y]

/-- Strict unsigned comparison is the negation of the reversed non-strict comparison. -/
def routingLTFlag (x y : List Bool) : List Bool := notBit (routingLEFlag y x)

/-- Numeric equality permits unequal word widths and arbitrary high zero padding. -/
def routingEQFlag (x y : List Bool) : List Bool :=
  andBit (routingLEFlag x y) (routingLEFlag y x)

/-- Multiply a binary word by three using one shift and one addition. -/
def routingTripleBits (bits : List Bool) : List Bool := routingAddBits bits (false :: bits)

/-- Multiply a binary word by six by shifting its triple once. -/
def routingSixBits (bits : List Bool) : List Bool := false :: routingTripleBits bits

/-- Addition reserves one more output bit than its longer operand. -/
@[simp] theorem routingAddBits_length (x y : List Bool) :
    (routingAddBits x y).length = max x.length y.length + 1 :=
  binaryCertificateAdd_length x y

/-- Addition has exact natural-number semantics, including on padded inputs. -/
theorem routingAddBits_value (x y : List Bool) :
    Nat.fromBitsLE (routingAddBits x y) = Nat.fromBitsLE x + Nat.fromBitsLE y :=
  binaryCertificateAdd_value x y

/-- Non-strict comparison always emits one Boolean flag. -/
@[simp] theorem routingLEFlag_length (x y : List Bool) : (routingLEFlag x y).length = 1 :=
  binaryCertificateLE_length x y

/-- Non-strict comparison accepts exactly the unsigned order relation. -/
theorem routingLEFlag_value (x y : List Bool) :
    routingLEFlag x y = [decide (Nat.fromBitsLE x ≤ Nat.fromBitsLE y)] :=
  binaryCertificateLE_value x y

/-- Strict comparison accepts exactly strict unsigned order. -/
theorem routingLTFlag_value (x y : List Bool) :
    routingLTFlag x y = [decide (Nat.fromBitsLE x < Nat.fromBitsLE y)] := by
  by_cases h : Nat.fromBitsLE y ≤ Nat.fromBitsLE x
  · have hn : ¬ Nat.fromBitsLE x < Nat.fromBitsLE y := by omega
    simp [routingLTFlag, routingLEFlag_value, h, hn, notBit, caseBit₀]
  · have hl : Nat.fromBitsLE x < Nat.fromBitsLE y := by omega
    simp [routingLTFlag, routingLEFlag_value, h, hl, notBit, caseBit₀]

/-- Numeric equality accepts exactly equal decoded values, independently of padding. -/
theorem routingEQFlag_value (x y : List Bool) :
    routingEQFlag x y = [decide (Nat.fromBitsLE x = Nat.fromBitsLE y)] := by
  by_cases he : Nat.fromBitsLE x = Nat.fromBitsLE y
  · simp [routingEQFlag, routingLEFlag_value, he, andBit, caseBit₀]
  · by_cases hxy : Nat.fromBitsLE x ≤ Nat.fromBitsLE y
    · have hyx : ¬ Nat.fromBitsLE y ≤ Nat.fromBitsLE x := by omega
      simp [routingEQFlag, routingLEFlag_value, hxy, hyx, he, andBit, caseBit₀]
    · simp [routingEQFlag, routingLEFlag_value, hxy, he, andBit, caseBit₀]

/-- Numeric equality always emits one Boolean flag. -/
@[simp] theorem routingEQFlag_length (x y : List Bool) : (routingEQFlag x y).length = 1 := by
  rw [routingEQFlag_value]
  rfl

/-- Strict comparison always emits one Boolean flag. -/
@[simp] theorem routingLTFlag_length (x y : List Bool) : (routingLTFlag x y).length = 1 := by
  rw [routingLTFlag_value]
  rfl

/-- Tripling reserves two extra bits for the shifted operand and the carry. -/
@[simp] theorem routingTripleBits_length (bits : List Bool) :
    (routingTripleBits bits).length = bits.length + 2 := by
  simp [routingTripleBits]

/-- Tripling decodes to exact multiplication by three. -/
theorem routingTripleBits_value (bits : List Bool) :
    Nat.fromBitsLE (routingTripleBits bits) = 3 * Nat.fromBitsLE bits := by
  rw [routingTripleBits, routingAddBits_value, Nat.fromBitsLE_cons]
  simp only [Bool.false_eq_true, ite_false]
  omega

/-- Multiplication by six reserves three extra bits. -/
@[simp] theorem routingSixBits_length (bits : List Bool) :
    (routingSixBits bits).length = bits.length + 3 := by simp [routingSixBits]

/-- Multiplication by six has exact natural-number semantics. -/
theorem routingSixBits_value (bits : List Bool) :
    Nat.fromBitsLE (routingSixBits bits) = 6 * Nat.fromBitsLE bits := by
  rw [routingSixBits, Nat.fromBitsLE_cons, routingTripleBits_value]
  simp only [Bool.false_eq_true, ite_false]
  omega

/-- Addition composes arbitrary polynomial-time word producers. -/
theorem routingAddBitsFn_mem_FP {x y : List Bool → List Bool} (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => routingAddBits (x z) (y z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.comp₂ (cobham_iff_FPn.mpr binaryCertificateAdd_mem_FPn)
    (FP_subset_CobhamFP hx) (FP_subset_CobhamFP hy)

/-- Unsigned comparison composes arbitrary polynomial-time word producers. -/
theorem routingLEFlagFn_mem_FP {x y : List Bool → List Bool} (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => routingLEFlag (x z) (y z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.comp₂ (cobham_iff_FPn.mpr binaryCertificateLE_mem_FPn)
    (FP_subset_CobhamFP hx) (FP_subset_CobhamFP hy)

/-- Strict comparison composes the comparator machine with Boolean negation. -/
theorem routingLTFlagFn_mem_FP {x y : List Bool → List Bool} (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => routingLTFlag (x z) (y z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.notFn (FP_subset_CobhamFP (routingLEFlagFn_mem_FP hy hx))

/-- Numeric equality composes two unsigned comparison machines and conjunction. -/
theorem routingEQFlagFn_mem_FP {x y : List Bool → List Bool} (hx : x ∈ FP) (hy : y ∈ FP) :
    (fun z => routingEQFlag (x z) (y z)) ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.andFn (FP_subset_CobhamFP (routingLEFlagFn_mem_FP hx hy))
    (FP_subset_CobhamFP (routingLEFlagFn_mem_FP hy hx))

private theorem shiftFn_mem_FP {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    (fun z => false :: bits z) ∈ FP := by
  apply CobhamFP_subset_FP
  exact Cobham.comp (.bit false) (fun _ => FP_subset_CobhamFP hb)

/-- Tripling is uniformly polynomial-time in its binary word producer. -/
theorem routingTripleBitsFn_mem_FP {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    (fun z => routingTripleBits (bits z)) ∈ FP :=
  routingAddBitsFn_mem_FP hb (shiftFn_mem_FP hb)

/-- Multiplication by six is uniformly polynomial-time in its binary word producer. -/
theorem routingSixBitsFn_mem_FP {bits : List Bool → List Bool} (hb : bits ∈ FP) :
    (fun z => routingSixBits (bits z)) ∈ FP :=
  shiftFn_mem_FP (routingTripleBitsFn_mem_FP hb)

end GameTheory.Complexity.Backend
