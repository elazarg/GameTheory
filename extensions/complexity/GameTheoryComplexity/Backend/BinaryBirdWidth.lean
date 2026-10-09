import GameTheoryComplexity.Backend.BinarySignedFixedWidth
import GameTheory.Math.BirdIterationBounds

/-! Polynomial length rulers for exact division-free matrix arithmetic. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- A ruler for the uniform stage magnitude bound. Arguments are dimension and input bit width. -/
def binaryBirdStageWidth (v : Fin 2 → List Bool) : List Bool :=
  smash (v 0 ++ [true]) (v 1 ++ v 0 ++ [true, true]) ++ [true]

theorem binaryBirdStageWidth_length (v : Fin 2 → List Bool) :
    (binaryBirdStageWidth v).length = GameTheory.Math.BirdIterationBounds.width
      (v 0).length (v 1).length := by
  simp [binaryBirdStageWidth, smash_length, GameTheory.Math.BirdIterationBounds.width]
  omega

theorem binaryBirdStageWidth_cobham : Cobham binaryBirdStageWidth :=
  Cobham.appendFn (Cobham.comp₂ Cobham.smash
    (Cobham.appendFn (.proj 0) (Cobham.const [true]))
    (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 0)) (Cobham.const [true, true])))
    (Cobham.const [true])

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

theorem binaryBirdWorkWidth_cobham : Cobham binaryBirdWorkWidth :=
  Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn
    (Cobham.appendFn binaryBirdStageWidth_cobham binaryBirdStageWidth_cobham) (.proj 1))
    (.proj 0)) (.proj 0)) (Cobham.const [true, true, true, true, true, true])

theorem binaryBirdWorkWidth_mem_FPn : FPn binaryBirdWorkWidth :=
  cobham_iff_FPn.mp binaryBirdWorkWidth_cobham

end GameTheory.Complexity.Backend
