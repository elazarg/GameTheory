import GameTheory.Model.SemanticForm

namespace GameTheory
namespace InfoModel

variable {ι : Type} {M : LSM ι} (I : InfoModel M)

theorem projectStates_cons (i : ι) (s : M.State) (ss : List M.State) :
    I.projectStates i (s :: ss) = I.observe i s :: I.projectStates i ss := by
  rfl

theorem projectStates_snoc (i : ι) (ss : List M.State) (t : M.State) :
    I.projectStates i (ss ++ [t]) = I.projectStates i ss ++ [I.observe i t] := by
  simp [InfoModel.projectStates, List.map_append]

theorem projectStates_length (i : ι) (ss : List M.State) :
    (I.projectStates i ss).length = ss.length := by
  simp [InfoModel.projectStates]

theorem projectStates_take_strict_mono_len
    (i : ι) (ss : List M.State) {j₁ j₂ : Nat}
    (hj : j₁ < j₂) (hlen : j₂ < ss.length) :
    (I.projectStates i (ss.take (j₁ + 1))).length <
      (I.projectStates i (ss.take (j₂ + 1))).length := by
  have hj1le : j₁ + 1 ≤ ss.length := Nat.succ_le_of_lt (lt_trans hj hlen)
  have hj2le : j₂ + 1 ≤ ss.length := Nat.succ_le_of_lt hlen
  simpa [InfoModel.projectStates, List.length_take, hj1le, hj2le] using Nat.succ_lt_succ hj

theorem projectStates_take_ne_of_lt
    (i : ι) (ss : List M.State) {j₁ j₂ : Nat}
    (hj : j₁ < j₂) (hlen : j₂ < ss.length) :
    I.projectStates i (ss.take (j₁ + 1)) ≠ I.projectStates i (ss.take (j₂ + 1)) := by
  intro hEq
  have hlenEq := congrArg List.length hEq
  have hj1le : j₁ + 1 ≤ ss.length := Nat.succ_le_of_lt (lt_trans hj hlen)
  have hj2le : j₂ + 1 ≤ ss.length := Nat.succ_le_of_lt hlen
  have : j₁ + 1 = j₂ + 1 := by
    simpa [InfoModel.projectStates, List.length_take, hj1le, hj2le] using hlenEq
  exact Nat.ne_of_lt hj (Nat.succ.inj this)

theorem outcomeOfStates_apply (ss : List M.State) (i : ι) :
    I.outcomeOfStates ss i = I.projectStates i ss := by
  rfl

end InfoModel
end GameTheory

