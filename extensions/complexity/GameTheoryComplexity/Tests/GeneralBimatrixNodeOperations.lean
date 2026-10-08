import GameTheoryComplexity.Backend.GeneralBimatrixNodeOperations

namespace GameTheory.Complexity.Tests.GeneralBimatrixNodeOperations
open Backend GameTheory.Finite GameTheory.Finite.BimatrixPathBinaryCodec
open _root_.Complexity _root_.Complexity.Cobham

private def input : List Bool := encodeGeneralInstance 1 1 1 (fun _ _ => 0) (fun _ _ => 0)

example : FPn generalBimatrixPivotWord := generalBimatrixPivotWord_mem_FPn
example : FPn generalBimatrixSwitchWord := generalBimatrixSwitchWord_mem_FPn

-- The source port is a switching endpoint for the decoded one-by-one game.
example : generalBimatrixSwitchWord ![input, List.replicate 8 false] = List.replicate 8 false := by
  decide +kernel

-- The actual integer dictionary selects the other label's slack at the source.
/-- info: true -/
#guard_msgs in
#eval generalBimatrixPivotWord ![input, List.replicate 8 false] ==
  [false, true, true, false, false, true, true, false]

-- Actual dictionary selection also reverses the source pivot.
/-- info: true -/
#guard_msgs in
#eval generalBimatrixPivotWord ![input,
  generalBimatrixPivotWord ![input, List.replicate 8 false]] == List.replicate 8 false

-- Invalid node widths retain their exact contents.
example : generalBimatrixSwitchWord ![input, [true, false]] = [true, false] := by decide +kernel
example : generalBimatrixPivotWord ![[], [true, false]] = [true, false] := by decide +kernel
example : generalBimatrixPivotWord ![[], []] = [] := by decide +kernel

-- Length preservation holds even if the selector sees no eligible direction.
example (instanceWord node : List Bool) :
    (generalBimatrixPivotWord ![instanceWord, node]).length = node.length :=
  generalBimatrixPivotWord_length _
example (instanceWord node : List Bool) :
    (generalBimatrixSwitchWord ![instanceWord, node]).length = node.length :=
  generalBimatrixSwitchWord_length _

end GameTheory.Complexity.Tests.GeneralBimatrixNodeOperations