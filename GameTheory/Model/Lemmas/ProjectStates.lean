import GameTheory.Model.SemanticForm

namespace GameTheory
namespace InfoModel

variable {ι : Type} {M : LSM ι} (I : InfoModel M)

theorem projectPublic_cons (s : M.State) (ss : List M.State) :
    I.projectPublic (s :: ss) = I.publicView s :: I.projectPublic ss := by
  rfl

theorem projectPrivate_cons (i : ι) (s : M.State) (ss : List M.State) :
    I.projectPrivate i (s :: ss) = I.observe i s :: I.projectPrivate i ss := by
  rfl

theorem projectStates_cons (i : ι) (s : M.State) (ss : List M.State) :
    I.projectStates i (s :: ss) =
      (I.publicView s :: I.projectPublic ss, I.observe i s :: I.projectPrivate i ss) := by
  rfl

theorem projectPublic_snoc (ss : List M.State) (t : M.State) :
    I.projectPublic (ss ++ [t]) = I.projectPublic ss ++ [I.publicView t] := by
  simp [InfoModel.projectPublic, List.map_append]

theorem projectPrivate_snoc (i : ι) (ss : List M.State) (t : M.State) :
    I.projectPrivate i (ss ++ [t]) = I.projectPrivate i ss ++ [I.observe i t] := by
  simp [InfoModel.projectPrivate, List.map_append]

theorem projectStates_snoc (i : ι) (ss : List M.State) (t : M.State) :
    I.projectStates i (ss ++ [t]) =
      (I.projectPublic ss ++ [I.publicView t], I.projectPrivate i ss ++ [I.observe i t]) := by
  simp [InfoModel.projectStates, projectPublic_snoc, projectPrivate_snoc]

theorem projectPublic_length (ss : List M.State) :
    (I.projectPublic ss).length = ss.length := by
  simp [InfoModel.projectPublic]

theorem projectPrivate_length (i : ι) (ss : List M.State) :
    (I.projectPrivate i ss).length = ss.length := by
  simp [InfoModel.projectPrivate]

theorem projectStates_lengths (i : ι) (ss : List M.State) :
    (I.projectStates i ss).1.length = ss.length ∧ (I.projectStates i ss).2.length = ss.length := by
  simp [InfoModel.projectStates, projectPublic_length, projectPrivate_length]

theorem projectPublic_take (ss : List M.State) (n : Nat) :
    I.projectPublic (ss.take n) = (I.projectPublic ss).take n := by
  simp [InfoModel.projectPublic, List.map_take]

theorem projectPrivate_take (i : ι) (ss : List M.State) (n : Nat) :
    I.projectPrivate i (ss.take n) = (I.projectPrivate i ss).take n := by
  simp [InfoModel.projectPrivate, List.map_take]

theorem projectStates_take (i : ι) (ss : List M.State) (n : Nat) :
    I.projectStates i (ss.take n) =
      ((I.projectStates i ss).1.take n, (I.projectStates i ss).2.take n) := by
  simp [InfoModel.projectStates, projectPublic_take, projectPrivate_take]

theorem projectPrivate_take_strict_mono_len
    (i : ι) (ss : List M.State) {j₁ j₂ : Nat}
    (hj : j₁ < j₂) (hlen : j₂ < ss.length) :
    (I.projectPrivate i (ss.take (j₁ + 1))).length <
      (I.projectPrivate i (ss.take (j₂ + 1))).length := by
  have hj1le : j₁ + 1 ≤ ss.length := Nat.succ_le_of_lt (lt_trans hj hlen)
  have hj2le : j₂ + 1 ≤ ss.length := Nat.succ_le_of_lt hlen
  simpa [InfoModel.projectPrivate, List.length_take, hj1le, hj2le] using Nat.succ_lt_succ hj

theorem projectPrivate_take_ne_of_lt
    (i : ι) (ss : List M.State) {j₁ j₂ : Nat}
    (hj : j₁ < j₂) (hlen : j₂ < ss.length) :
    I.projectPrivate i (ss.take (j₁ + 1)) ≠ I.projectPrivate i (ss.take (j₂ + 1)) := by
  intro hEq
  have hlenEq := congrArg List.length hEq
  have hj1le : j₁ + 1 ≤ ss.length := Nat.succ_le_of_lt (lt_trans hj hlen)
  have hj2le : j₂ + 1 ≤ ss.length := Nat.succ_le_of_lt hlen
  have : j₁ + 1 = j₂ + 1 := by
    simpa [InfoModel.projectPrivate, List.length_take, hj1le, hj2le] using hlenEq
  exact Nat.ne_of_lt hj (Nat.succ.inj this)

theorem outcomeOfStates_fst (ss : List M.State) :
    (I.outcomeOfStates ss).1 = I.projectPublic ss := by
  rfl

theorem outcomeOfStates_snd_apply (ss : List M.State) (i : ι) :
    (I.outcomeOfStates ss).2 i = I.projectPrivate i ss := by
  rfl

theorem projectPublic_getLast? (ss : List M.State) :
    (I.projectPublic ss).getLast? = Option.map I.publicView ss.getLast? := by
  induction ss with
  | nil =>
      rfl
  | cons s tl ih =>
      cases tl with
      | nil =>
          simp [InfoModel.projectPublic]
      | cons s' tl' =>
          simpa [InfoModel.projectPublic] using ih

theorem projectPrivate_getLast? (i : ι) (ss : List M.State) :
    (I.projectPrivate i ss).getLast? = Option.map (I.observe i) ss.getLast? := by
  induction ss with
  | nil =>
      rfl
  | cons s tl ih =>
      cases tl with
      | nil =>
          simp [InfoModel.projectPrivate]
      | cons s' tl' =>
          simpa [InfoModel.projectPrivate] using ih

theorem projectStates_getLast? (i : ι) (ss : List M.State) :
    (I.projectStates i ss).1.getLast? = Option.map I.publicView ss.getLast? ∧
      (I.projectStates i ss).2.getLast? = Option.map (I.observe i) ss.getLast? := by
  simp [InfoModel.projectStates, projectPublic_getLast?, projectPrivate_getLast?]

end InfoModel
end GameTheory
