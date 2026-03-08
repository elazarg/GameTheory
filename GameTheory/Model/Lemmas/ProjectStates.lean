import GameTheory.Model.SemanticForm

namespace GameTheory
namespace InfoModel

variable {ι σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)

theorem projectPublic_cons (s : σ) (ss : List σ) :
    I.projectPublic (s :: ss) = I.publicView s :: I.projectPublic ss := by
  rfl

theorem projectPrivate_cons (i : ι) (s : σ) (ss : List σ) :
    I.projectPrivate i (s :: ss) = I.observe i s :: I.projectPrivate i ss := by
  rfl

theorem projectStates_cons (i : ι) (s : σ) (ss : List σ) :
    I.projectStates i (s :: ss) =
      (I.publicView s :: I.projectPublic ss, I.observe i s :: I.projectPrivate i ss) := by
  rfl

theorem projectPublic_snoc (ss : List σ) (t : σ) :
    I.projectPublic (ss ++ [t]) = I.projectPublic ss ++ [I.publicView t] := by
  simp [InfoModel.projectPublic, List.map_append]

theorem projectPrivate_snoc (i : ι) (ss : List σ) (t : σ) :
    I.projectPrivate i (ss ++ [t]) = I.projectPrivate i ss ++ [I.observe i t] := by
  simp [InfoModel.projectPrivate, List.map_append]

theorem projectStates_snoc (i : ι) (ss : List σ) (t : σ) :
    I.projectStates i (ss ++ [t]) =
      (I.projectPublic ss ++ [I.publicView t], I.projectPrivate i ss ++ [I.observe i t]) := by
  simp [InfoModel.projectStates, projectPublic_snoc, projectPrivate_snoc]

theorem projectPublic_length (ss : List σ) :
    (I.projectPublic ss).length = ss.length := by
  simp [InfoModel.projectPublic]

theorem projectPrivate_length (i : ι) (ss : List σ) :
    (I.projectPrivate i ss).length = ss.length := by
  simp [InfoModel.projectPrivate]

theorem projectStates_lengths (i : ι) (ss : List σ) :
    (I.projectStates i ss).1.length = ss.length ∧ (I.projectStates i ss).2.length = ss.length := by
  simp [InfoModel.projectStates, projectPublic_length, projectPrivate_length]

theorem projectPublic_take (ss : List σ) (n : Nat) :
    I.projectPublic (ss.take n) = (I.projectPublic ss).take n := by
  simp [InfoModel.projectPublic, List.map_take]

theorem projectPrivate_take (i : ι) (ss : List σ) (n : Nat) :
    I.projectPrivate i (ss.take n) = (I.projectPrivate i ss).take n := by
  simp [InfoModel.projectPrivate, List.map_take]

theorem projectStates_take (i : ι) (ss : List σ) (n : Nat) :
    I.projectStates i (ss.take n) =
      ((I.projectStates i ss).1.take n, (I.projectStates i ss).2.take n) := by
  simp [InfoModel.projectStates, projectPublic_take, projectPrivate_take]

theorem projectPrivate_take_strict_mono_len
    (i : ι) (ss : List σ) {j₁ j₂ : Nat}
    (hj : j₁ < j₂) (hlen : j₂ < ss.length) :
    (I.projectPrivate i (ss.take (j₁ + 1))).length <
      (I.projectPrivate i (ss.take (j₂ + 1))).length := by
  have hj1le : j₁ + 1 ≤ ss.length := Nat.succ_le_of_lt (lt_trans hj hlen)
  have hj2le : j₂ + 1 ≤ ss.length := Nat.succ_le_of_lt hlen
  simpa [InfoModel.projectPrivate, List.length_take, hj1le, hj2le] using Nat.succ_lt_succ hj

theorem projectPrivate_take_ne_of_lt
    (i : ι) (ss : List σ) {j₁ j₂ : Nat}
    (hj : j₁ < j₂) (hlen : j₂ < ss.length) :
    I.projectPrivate i (ss.take (j₁ + 1)) ≠ I.projectPrivate i (ss.take (j₂ + 1)) := by
  intro hEq
  have hlenEq := congrArg List.length hEq
  have hj1le : j₁ + 1 ≤ ss.length := Nat.succ_le_of_lt (lt_trans hj hlen)
  have hj2le : j₂ + 1 ≤ ss.length := Nat.succ_le_of_lt hlen
  have : j₁ + 1 = j₂ + 1 := by
    simpa [InfoModel.projectPrivate, List.length_take, hj1le, hj2le] using hlenEq
  exact Nat.ne_of_lt hj (Nat.succ.inj this)

theorem outcomeOfStates_fst (ss : List σ) :
    (I.outcomeOfStates ss).1 = I.projectPublic ss := by
  rfl

theorem outcomeOfStates_snd_apply (ss : List σ) (i : ι) :
    (I.outcomeOfStates ss).2 i = I.projectPrivate i ss := by
  rfl

theorem projectPublic_getLast? (ss : List σ) :
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

theorem projectPrivate_getLast? (i : ι) (ss : List σ) :
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

theorem projectStates_getLast? (i : ι) (ss : List σ) :
    (I.projectStates i ss).1.getLast? = Option.map I.publicView ss.getLast? ∧
      (I.projectStates i ss).2.getLast? = Option.map (I.observe i) ss.getLast? := by
  simp [InfoModel.projectStates, projectPublic_getLast?, projectPrivate_getLast?]

/-- Equal trace projections imply equal trace lengths (via public component). -/
theorem projectStates_eq_length (i : ι) {ss₁ ss₂ : List σ}
    (h : I.projectStates i ss₁ = I.projectStates i ss₂) :
    ss₁.length = ss₂.length := by
  have := congr_arg (fun p => p.1.length) h
  simp only [InfoModel.projectStates, InfoModel.projectPublic, List.length_map] at this
  exact this

/-- Equal trace projections imply obs-equivalent endpoints (or `I.init` fallback). -/
theorem obsEq_of_projectStates_getLast (i : ι) {ss ss' : List σ}
    (hproj : I.projectStates i ss = I.projectStates i ss') :
    I.obsEq i (ss.getLast?.getD I.init) (ss'.getLast?.getD I.init) := by
  unfold InfoModel.projectStates InfoModel.projectPublic InfoModel.projectPrivate at hproj
  have hpub := (Prod.ext_iff.mp hproj).1
  have hpriv := (Prod.ext_iff.mp hproj).2
  constructor
  · have := congr_arg List.getLast? hpub
    simp only [List.getLast?_map] at this
    cases hss : ss.getLast? <;> cases hss' : ss'.getLast? <;> simp_all [Option.map]
  · have := congr_arg List.getLast? hpriv
    simp only [List.getLast?_map] at this
    cases hss : ss.getLast? <;> cases hss' : ss'.getLast? <;> simp_all [Option.map]

/-- Append decomposition: `projectStates i (p ++ [t]) = projectStates i (p' ++ [t'])`
    implies both prefix and endpoint equalities. -/
theorem projectStates_append_singleton_eq
    (i : ι) {p p' : List σ} {t t' : σ}
    (h : I.projectStates i (p ++ [t]) = I.projectStates i (p' ++ [t'])) :
    I.projectStates i p = I.projectStates i p' ∧ I.obsEq i t t' := by
  simp only [InfoModel.projectStates, InfoModel.projectPublic, InfoModel.projectPrivate,
    List.map_append, List.map_cons, List.map_nil] at h
  have hpub_p := List.append_inj_left' (congr_arg Prod.fst h) (by simp)
  have hpriv_p := List.append_inj_left' (congr_arg Prod.snd h) (by simp)
  have hpub_t := List.append_inj_right' (congr_arg Prod.fst h) (by simp)
  have hpriv_t := List.append_inj_right' (congr_arg Prod.snd h) (by simp)
  exact ⟨Prod.ext hpub_p hpriv_p, ⟨by simpa using hpub_t, by simpa using hpriv_t⟩⟩

/-- Prefix extraction from append: `projectStates i (p ++ [t]) = projectStates i (p' ++ [t'])`
    implies `projectStates i p = projectStates i p'`. -/
theorem projectStates_prefix_of_append
    (i : ι) {p p' : List σ} {t t' : σ}
    (h : I.projectStates i (p ++ [t]) = I.projectStates i (p' ++ [t'])) :
    I.projectStates i p = I.projectStates i p' :=
  (projectStates_append_singleton_eq I i h).1

/-- Endpoint obsEq from append: `projectStates i (p ++ [t]) = projectStates i (p' ++ [t'])`
    implies `obsEq i t t'`. -/
theorem obsEq_of_projectStates_append
    (i : ι) {p p' : List σ} {t t' : σ}
    (h : I.projectStates i (p ++ [t]) = I.projectStates i (p' ++ [t'])) :
    I.obsEq i t t' :=
  (projectStates_append_singleton_eq I i h).2

theorem projectActions_snoc (i : ι) (ha : List I.JointAction) (a : I.JointAction) :
    I.projectActions i (ha ++ [a]) = I.projectActions i ha ++ [a i] := by
  simp [InfoModel.projectActions, List.map_append]

/-- Equal `projectActions` on appended singletons implies equal last actions. -/
theorem projectActions_last_eq (i : ι) {ha ha' : List I.JointAction}
    {a a' : I.JointAction}
    (h : I.projectActions i (ha ++ [a]) = I.projectActions i (ha' ++ [a'])) :
    a i = a' i := by
  rw [projectActions_snoc, projectActions_snoc] at h
  exact List.cons.inj (List.append_inj_right' h (by simp)) |>.1

end InfoModel
end GameTheory
