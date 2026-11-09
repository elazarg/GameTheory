module

public import GameTheoryComplexity.Backend.BinarySignedFixedWidth
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import GameTheory.Math.BirdIterationBounds

@[expose] public section

/-! Polynomial length rulers for exact division-free matrix arithmetic. -/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM

/-- A ruler for the uniform stage magnitude bound. Arguments are dimension and input bit width. -/
def binaryBirdStageWidth (v : Fin 2 → List Bool) : List Bool :=
  List.replicate ((v 0).length.succ * ((v 1).length + (v 0).length + 2)) true ++ [true]

theorem binaryBirdStageWidth_length (v : Fin 2 → List Bool) :
    (binaryBirdStageWidth v).length = GameTheory.Math.BirdIterationBounds.width
      (v 0).length (v 1).length := by
  simp [binaryBirdStageWidth, GameTheory.Math.BirdIterationBounds.width]

@[fun_prop] theorem binaryBirdStageWidth_polyTime :
    ComputableInPolyTime binaryBirdStageWidth (encPi encBits) encBits := by
  have hn : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hh : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hnLength := ComputableInPolyTime.length_bits_comp hn
  have hhLength := ComputableInPolyTime.length_bits_comp hh
  have hnSucc := ComputableInPolyTime.unary_add' hnLength (.const 1)
  have hhPlusN := ComputableInPolyTime.unary_add' hhLength hnLength
  have hfactor := ComputableInPolyTime.unary_add' hhPlusN (.const 2)
  have hcount := ComputableInPolyTime.unary_mul' hnSucc hfactor
  exact ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsReplicate true |>.comp hcount)
    (.const [true])

/-- Extra capacity controls sums and products before cancellation. -/
def binaryBirdWorkWidth (v : Fin 2 → List Bool) : List Bool :=
  binaryBirdStageWidth v ++ binaryBirdStageWidth v ++ v 1 ++ v 0 ++ v 0 ++
    [true, true, true, true, true, true]

theorem binaryBirdWorkWidth_length (v : Fin 2 → List Bool) :
    (binaryBirdWorkWidth v).length = GameTheory.Math.BirdIterationBounds.workWidth
      (v 0).length (v 1).length := by
  simp only [binaryBirdWorkWidth, List.length_append, binaryBirdStageWidth_length,
    GameTheory.Math.BirdIterationBounds.workWidth]
  simp only [List.length_cons, List.length_nil]
  omega

@[fun_prop] theorem binaryBirdWorkWidth_polyTime :
    ComputableInPolyTime binaryBirdWorkWidth (encPi encBits) encBits := by
  have hstage := binaryBirdStageWidth_polyTime
  have hn : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 0)
      (encPi encBits) encBits := .pi_apply encBits 0
  have hh : ComputableInPolyTime (fun v : Fin 2 → List Bool => v 1)
      (encPi encBits) encBits := .pi_apply encBits 1
  have hss := ComputableInPolyTime.bitsAppend hstage hstage
  have hssh := ComputableInPolyTime.bitsAppend hss hh
  have hsshn := ComputableInPolyTime.bitsAppend hssh hn
  have hsshnn := ComputableInPolyTime.bitsAppend hsshn hn
  exact ComputableInPolyTime.bitsAppend hsshnn (.const [true, true, true, true, true, true])

end GameTheory.Complexity.Backend
