import GameTheoryComplexity.Backend.GeneralBimatrixCodec
import GameTheoryComplexity.Backend.BinarySignedFixedWidth

/-! Polynomial emission of the unsigned positive and negative payoff fields used by
rectangular game inputs. Arithmetic sign-header words remain internal to the writer. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Emit one fixed-width magnitude field, zeroing the field with the opposite sign. -/
def generalSignedMagnitude (positive : Bool) (ruler word : List Bool) : List Bool :=
  padTo ruler (caseBit₀ word (if positive then [] else word.tail)
    (if positive then word.tail else []))

@[simp] theorem generalSignedMagnitude_length (positive : Bool) (ruler word : List Bool) :
    (generalSignedMagnitude positive ruler word).length = ruler.length := padTo_length _ _

/-- The two emitted magnitude fields preserve every representable signed value. -/
theorem generalSignedMagnitude_value (ruler word : List Bool)
    (hfit : (binarySignedValue word).natAbs < 2 ^ ruler.length) :
    (Nat.fromBitsLE (generalSignedMagnitude true ruler word) : ℤ) -
      (Nat.fromBitsLE (generalSignedMagnitude false ruler word) : ℤ) =
        binarySignedValue word := by
  have hm : Nat.fromBitsLE word.tail < 2 ^ ruler.length := by
    simpa only [binarySignedValue_natAbs] using hfit
  have hzero : Nat.fromBitsLE ([] : List Bool) = 0 := rfl
  cases word with
  | nil => simp [generalSignedMagnitude, binarySignedValue, padTo_fromBitsLE, hzero]
  | cons b word =>
    simp only [List.tail_cons] at hm
    cases b <;> simp [generalSignedMagnitude, binarySignedValue, padTo_fromBitsLE,
      Nat.mod_eq_of_lt hm, hzero]

/-- Magnitude selection and fixed-width padding have an actual polynomial-time certificate. -/
theorem generalSignedMagnitude_cobham (positive : Bool) :
    Cobham fun v : Fin 2 → List Bool => generalSignedMagnitude positive (v 0) (v 1) := by
  cases positive
  · exact Cobham.padFn (.proj 0) (Cobham.iteFn (.proj 1)
      (Cobham.tailFn (.proj 1)) Cobham.empty)
  · exact Cobham.padFn (.proj 0) (Cobham.iteFn (.proj 1)
      Cobham.empty (Cobham.tailFn (.proj 1)))

theorem generalSignedMagnitude_mem_FPn (positive : Bool) :
    FPn (fun v : Fin 2 → List Bool => generalSignedMagnitude positive (v 0) (v 1)) :=
  cobham_iff_FPn.mp (generalSignedMagnitude_cobham positive)
end GameTheory.Complexity.Backend
