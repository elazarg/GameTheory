module

public import GameTheoryComplexity.Backend.GeneralBimatrixNodeColor
public import GameTheoryComplexity.Backend.GeneralBimatrixNodeOperations
public import GameTheory.Finite.BimatrixPathEndOfLine
public import GameTheoryComplexity.Backend.WordOperations

@[expose] public section

/-! Polynomial predecessor and successor machines for complementary paths.
Invalid vertex words are isolated by identity pointers. Valid words alternate
the certified pivot and internal switch using their computed orientation. -/
namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations

/-- The outgoing pointer of the oriented complementary path. -/
def generalBimatrixSuccessorWord (v : Fin 2 → List Bool) : List Bool :=
  select (generalBimatrixNodeValidFlag v)
    (select (generalBimatrixNodeColor v) (generalBimatrixPivotWord v)
      (generalBimatrixSwitchWord v)) (v 1)

/-- The incoming pointer of the oriented complementary path. -/
def generalBimatrixPredecessorWord (v : Fin 2 → List Bool) : List Bool :=
  select (generalBimatrixNodeValidFlag v)
    (select (generalBimatrixNodeColor v) (generalBimatrixSwitchWord v)
      (generalBimatrixPivotWord v)) (v 1)

private theorem select_length (flag x y : List Bool) (hx : x.length = y.length) :
    (select flag x y).length = y.length := by
  unfold select
  split
  · exact hx
  · rfl

theorem generalBimatrixSuccessorWord_length (v : Fin 2 → List Bool) :
    (generalBimatrixSuccessorWord v).length = (v 1).length := by
  apply select_length
  rw [select_length _ _ _ ((generalBimatrixPivotWord_length v).trans
    (generalBimatrixSwitchWord_length v).symm), generalBimatrixSwitchWord_length]

theorem generalBimatrixPredecessorWord_length (v : Fin 2 → List Bool) :
    (generalBimatrixPredecessorWord v).length = (v 1).length := by
  apply select_length
  rw [select_length _ _ _ ((generalBimatrixSwitchWord_length v).trans
    (generalBimatrixPivotWord_length v).symm), generalBimatrixPivotWord_length]

end GameTheory.Complexity.Backend

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
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
open Cslib.BitString Turing.MultiTapeTM
open GameTheory.Complexity.Backend.WordOperations
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
  cases hc : port.color <;> simp [select, BimatrixPathPort.successor,
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
  cases hc : port.color <;> simp [select, BimatrixPathPort.predecessor,
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

@[fun_prop] theorem generalBimatrixSuccessorWord_polyTime :
    ComputableInPolyTime generalBimatrixSuccessorWord (encPi encBits) encBits := by
  have hbranch := select_polyTime.comp
    (generalBimatrixNodeColor_polyTime.prod
      (generalBimatrixPivotWord_polyTime.prod generalBimatrixSwitchWord_polyTime))
  have hnode : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have h := select_polyTime.comp (generalBimatrixNodeValidFlag_polyTime.prod (hbranch.prod hnode))
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixSuccessorWord)
  intro v
  rfl

@[fun_prop] theorem generalBimatrixPredecessorWord_polyTime :
    ComputableInPolyTime generalBimatrixPredecessorWord (encPi encBits) encBits := by
  have hbranch := select_polyTime.comp
    (generalBimatrixNodeColor_polyTime.prod
      (generalBimatrixSwitchWord_polyTime.prod generalBimatrixPivotWord_polyTime))
  have hnode : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have h := select_polyTime.comp (generalBimatrixNodeValidFlag_polyTime.prod (hbranch.prod hnode))
  apply ComputableInPolyTime.of_tidy
  apply h.tidy.of_enc_eq (g := generalBimatrixPredecessorWord)
  intro v
  rfl

end GameTheory.Complexity.Backend
