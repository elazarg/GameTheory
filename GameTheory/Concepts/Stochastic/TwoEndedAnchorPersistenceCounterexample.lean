import Mathlib.Tactic

/-!
# Two-ended compactness does not preserve an anchor

This is the exact finite falsifier from Question 133.  The relation has two
points, all self-loops, and the one-way edge `false → true`, but no return
edge.  The finite paths spend longer and longer at each endpoint.  Their
forward windows converge to the `false` loop and their reverse windows to the
`true` loop, yet no exact loop at the forward anchor can contain the reverse
mark.
-/

set_option autoImplicit false

namespace GameTheory.TwoEndedAnchorPersistenceCounterexample

/-- The two-point exact relation: every edge except `true → false`. -/
def Rel (current successor : Bool) : Prop :=
  current = false ∨ successor = true

/-- The finite word `false^(m+1) true^(m+1)`, padded by `true` afterwards. -/
def finitePath (m time : ℕ) : Bool :=
  if time ≤ m then false else true

@[simp] theorem rel_false (successor : Bool) : Rel false successor := by
  exact Or.inl rfl

@[simp] theorem rel_true_iff (successor : Bool) :
    Rel true successor ↔ successor = true := by
  simp [Rel]

/-- Every adjacent pair in the finite family is an exact relation edge. -/
theorem finitePath_edge (m time : ℕ) :
    Rel (finitePath m time) (finitePath m (time + 1)) := by
  by_cases htime : time ≤ m
  · simp [finitePath, htime]
  · have hnext : ¬time + 1 ≤ m := by omega
    simp [finitePath, htime, hnext, Rel]

/-- Every fixed forward coordinate is eventually the `false` endpoint. -/
theorem finitePath_forward_eq_false {m time : ℕ} (htime : time ≤ m) :
    finitePath m time = false := by
  simp [finitePath, htime]

/-- At the designated endpoint `2m+1`, every reverse coordinate of depth at
most `m` is the `true` endpoint. -/
theorem finitePath_reverse_eq_true {m depth : ℕ} (hdepth : depth ≤ m) :
    finitePath m (2 * m + 1 - depth) = true := by
  have hfar : m < 2 * m + 1 - depth := by omega
  simp [finitePath, Nat.not_le.mpr hfar]

/-- Once an exact path reaches `true`, the one-way relation forces it to stay
there at every later displayed time. -/
theorem true_persists_along_exactPath
    (path : ℕ → Bool) (start finish : ℕ)
    (hedge : ∀ time, start ≤ time → time < finish →
      Rel (path time) (path (time + 1)))
    (hstart : path start = true) (hstartFinish : start ≤ finish) :
    path finish = true := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hstartFinish
  induction steps with
  | zero => simpa
  | succ steps ih =>
      have ih' : path (start + steps) = true :=
        ih (fun time hstartTime htime =>
          hedge time hstartTime (by omega)) (by omega)
      have hrel := hedge (start + steps) (by omega) (by omega)
      apply (rel_true_iff (path (start + steps + 1))).mp
      rw [← ih']
      simpa [Nat.add_assoc] using hrel

/-- **Anchor-persistence failure.**  No finite exact segment which begins and
ends at the forward anchor `false` can carry the reverse mark `true` at an
intermediate time. -/
theorem not_exists_false_loop_carrying_true_mark :
    ¬ ∃ (path : ℕ → Bool) (start marked finish : ℕ),
      start ≤ marked ∧ marked ≤ finish ∧
      path start = false ∧ path marked = true ∧ path finish = false ∧
      (∀ time, start ≤ time → time < finish →
        Rel (path time) (path (time + 1))) := by
  rintro ⟨path, start, marked, finish, _, hmarkedFinish, _,
    hmarked, hfinish, hedge⟩
  have := true_persists_along_exactPath path marked finish
    (fun time hmarkedTime htime => hedge time (by omega) htime)
    hmarked hmarkedFinish
  simp [hfinish] at this

/-- The missing executable return is already visible at one edge. -/
theorem not_rel_true_false : ¬Rel true false := by
  simp [Rel]

end GameTheory.TwoEndedAnchorPersistenceCounterexample
