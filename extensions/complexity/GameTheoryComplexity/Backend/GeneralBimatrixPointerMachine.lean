import GameTheoryComplexity.Backend.GeneralBimatrixNodeColor
import GameTheoryComplexity.Backend.GeneralBimatrixNodeOperations
import GameTheory.Finite.BimatrixPathEndOfLine

/-! Polynomial predecessor and successor machines for complementary paths.
Invalid vertex words are isolated by identity pointers. Valid words alternate
the certified pivot and internal switch using their computed orientation. -/
namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- The outgoing pointer of the oriented complementary path. -/
def generalBimatrixSuccessorWord (v : Fin 2 → List Bool) : List Bool :=
  caseBit₀ (generalBimatrixNodeValidFlag v)
    (caseBit₀ (generalBimatrixNodeColor v) (generalBimatrixPivotWord v)
      (generalBimatrixSwitchWord v)) (v 1)

/-- The incoming pointer of the oriented complementary path. -/
def generalBimatrixPredecessorWord (v : Fin 2 → List Bool) : List Bool :=
  caseBit₀ (generalBimatrixNodeValidFlag v)
    (caseBit₀ (generalBimatrixNodeColor v) (generalBimatrixSwitchWord v)
      (generalBimatrixPivotWord v)) (v 1)

theorem generalBimatrixSuccessorWord_cobham : Cobham generalBimatrixSuccessorWord :=
  Cobham.iteFn generalBimatrixNodeValidFlag_cobham
    (Cobham.iteFn generalBimatrixNodeColor_cobham generalBimatrixPivotWord_cobham
      generalBimatrixSwitchWord_cobham) (.proj 1)

theorem generalBimatrixPredecessorWord_cobham : Cobham generalBimatrixPredecessorWord :=
  Cobham.iteFn generalBimatrixNodeValidFlag_cobham
    (Cobham.iteFn generalBimatrixNodeColor_cobham generalBimatrixSwitchWord_cobham
      generalBimatrixPivotWord_cobham) (.proj 1)

private theorem case_length (flag x y : List Bool) (hx : x.length = y.length) :
    (caseBit₀ flag x y).length = y.length := by
  cases flag with
  | nil => rfl
  | cons b tail => cases b <;> simp [caseBit₀, hx]

theorem generalBimatrixSuccessorWord_length (v : Fin 2 → List Bool) :
    (generalBimatrixSuccessorWord v).length = (v 1).length := by
  apply case_length
  rw [case_length _ _ _ ((generalBimatrixPivotWord_length v).trans
    (generalBimatrixSwitchWord_length v).symm), generalBimatrixSwitchWord_length]

theorem generalBimatrixPredecessorWord_length (v : Fin 2 → List Bool) :
    (generalBimatrixPredecessorWord v).length = (v 1).length := by
  apply case_length
  rw [case_length _ _ _ ((generalBimatrixSwitchWord_length v).trans
    (generalBimatrixPivotWord_length v).symm), generalBimatrixPivotWord_length]

end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

/-- The existing path predecessor specialized to the decoded, shifted game. -/
noncomputable abbrev generalBimatrixPathPredecessor (input : List Bool)
    (hi : GeneralInstanceValid input)
    (d : Fin (generalRowCount input + generalColCount input)) :
    GeneralBimatrixShiftedPort input d → GeneralBimatrixShiftedPort input d :=
  BimatrixPathPort.predecessor hi.1 hi.2.1
    (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
    (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le)

/-- The existing path successor specialized to the decoded, shifted game. -/
noncomputable abbrev generalBimatrixPathSuccessor (input : List Bool)
    (hi : GeneralInstanceValid input)
    (d : Fin (generalRowCount input + generalColCount input)) :
    GeneralBimatrixShiftedPort input d → GeneralBimatrixShiftedPort input d :=
  BimatrixPathPort.successor hi.1 hi.2.1
    (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
    (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le)

end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec

/-- Exact machine agreement at a validated canonical vertex. -/
theorem generalBimatrixSuccessorWord_encode_of_valid (input : List Bool)
    (hi : GeneralInstanceValid input)
    {d : Fin (generalRowCount input + generalColCount input)} (hd : d.val = 0)
    (port : BimatrixPathPort
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1)) d)
    (hv : generalBimatrixNodeValidFlag ![input, encode port] = [true]) :
    generalBimatrixSuccessorWord ![input, encode port] = encode
      (BimatrixPathPort.successor hi.1 hi.2.1
        (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
        (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le) port) := by
  rw [generalBimatrixSuccessorWord, hv, generalBimatrixNodeColor_encode input hi hd port,
    generalBimatrixPivotWord_encode input hi hd port,
    generalBimatrixSwitchWord_encode input (generalBimatrixDimensionWord_length input) hd port]
  cases hc : port.color <;> simp [_root_.Complexity.caseBit₀, BimatrixPathPort.successor,
    GameTheory.Math.OrientedInvolutionPath.successor, hc]

/-- Exact incoming machine agreement at a validated canonical vertex. -/
theorem generalBimatrixPredecessorWord_encode_of_valid (input : List Bool)
    (hi : GeneralInstanceValid input)
    {d : Fin (generalRowCount input + generalColCount input)} (hd : d.val = 0)
    (port : BimatrixPathPort
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1)) d)
    (hv : generalBimatrixNodeValidFlag ![input, encode port] = [true]) :
    generalBimatrixPredecessorWord ![input, encode port] = encode
      (BimatrixPathPort.predecessor hi.1 hi.2.1
        (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt false input i.val j.val).le)
        (fun i j => payoff_add_pow_positive _ _ (decodeGeneralPayoff_natAbs_lt true input i.val j.val).le) port) := by
  rw [generalBimatrixPredecessorWord, hv, generalBimatrixNodeColor_encode input hi hd port,
    generalBimatrixPivotWord_encode input hi hd port,
    generalBimatrixSwitchWord_encode input (generalBimatrixDimensionWord_length input) hd port]
  cases hc : port.color <;> simp [_root_.Complexity.caseBit₀, BimatrixPathPort.predecessor,
    GameTheory.Math.OrientedInvolutionPath.predecessor, hc]

/-- Every word, including failed encodings, has the transported mathematical predecessor. -/
theorem generalBimatrixPredecessorWord_eq_transport (input node : List Bool)
    (hi : GeneralInstanceValid input)
    (d : Fin (generalRowCount input + generalColCount input)) (hd : d.val = 0) :
    generalBimatrixPredecessorWord ![input, node] =
      transport (generalBimatrixPathPredecessor input hi d) node := by
  cases hdecode : decode
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1)) d node with
  | none =>
    rw [transport_invalid _ hdecode, generalBimatrixPredecessorWord,
      generalBimatrixNodeValidFlag_eq_false_of_decode_none input node hi d hd hdecode]
    rfl
  | some port =>
    rw [← encode_of_decode_eq_some hdecode, transport_encode]
    exact generalBimatrixPredecessorWord_encode_of_valid input hi hd port
      (generalBimatrixNodeValidFlag_encode input hi hd port)

/-- Every word, including failed encodings, has the transported mathematical successor. -/
theorem generalBimatrixSuccessorWord_eq_transport (input node : List Bool)
    (hi : GeneralInstanceValid input)
    (d : Fin (generalRowCount input + generalColCount input)) (hd : d.val = 0) :
    generalBimatrixSuccessorWord ![input, node] =
      transport (generalBimatrixPathSuccessor input hi d) node := by
  cases hdecode : decode
      (fun i j => decodeGeneralPayoff false input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1))
      (fun i j => decodeGeneralPayoff true input i.val j.val +
        ((2 : ℤ) ^ generalCoefficientBits input + 1)) d node with
  | none =>
    rw [transport_invalid _ hdecode, generalBimatrixSuccessorWord,
      generalBimatrixNodeValidFlag_eq_false_of_decode_none input node hi d hd hdecode]
    rfl
  | some port =>
    rw [← encode_of_decode_eq_some hdecode, transport_encode]
    exact generalBimatrixSuccessorWord_encode_of_valid input hi hd port
      (generalBimatrixNodeValidFlag_encode input hi hd port)

end GameTheory.Complexity.Backend
