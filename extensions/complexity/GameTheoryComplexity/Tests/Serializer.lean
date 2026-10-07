import GameTheoryComplexity.Backend.Serializer

/-! Concrete controls for normalization, delimiter placement and zero parameter. -/

namespace GameTheory.Complexity.Backend

example : serializeBoolean ![[false, false], [false, true]] =
    [true, true, false, false, true] := rfl

example : serializeBoolean ![[], []] = [false] := rfl

example : booleanInput 0 0 (fun _ => true) = [false, true] := by
  simp [booleanInput, List.ofFn_succ]

end GameTheory.Complexity.Backend
