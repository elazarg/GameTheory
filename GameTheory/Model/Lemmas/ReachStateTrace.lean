import GameTheory.Model.SemanticForm

namespace GameTheory
namespace InfoModel

variable {ι : Type} {M : LSM ι}
variable {k : Nat} {h : List M.Label} {ss : List M.State}

theorem reachStateTrace_nonempty
    (hr : InfoModel.ReachStateTrace M h ss) :
    ss ≠ [] := by
  induction hr with
  | nil =>
      simp
  | snoc _ _ _ =>
      simp

theorem reachStateTrace_length_relation
    (hr : InfoModel.ReachStateTrace M h ss) :
    ss.length = h.length + 1 := by
  induction hr with
  | nil =>
      simp
  | snoc hr _ _ ih =>
      simp [List.length_append, ih, Nat.add_left_comm, Nat.add_comm]

/-- Convert a state-trace reach witness to action-erased label reachability at
the last state. -/
theorem reachStateTrace_to_reachBy
    (hr : InfoModel.ReachStateTrace M h ss) :
    ∃ s, ss.getLast? = some s ∧
      Semantics.Transition.ReachBy M.stepExists h M.init s := by
  induction hr with
  | nil =>
      exact ⟨M.init, rfl, Semantics.Transition.ReachBy.nil _⟩
  | @snoc h ss s t ℓ hr hlast hstep ih =>
      rcases ih with ⟨s0, hlast0, hreach0⟩
      have hs : s0 = s := by
        apply Option.some.inj
        calc
          some s0 = ss.getLast? := by simpa using hlast0.symm
          _ = some s := hlast
      refine ⟨t, by simp, ?_⟩
      have hreachs : Semantics.Transition.ReachBy M.stepExists h M.init s := by
        simpa [hs] using hreach0
      exact Semantics.Transition.reachBy_append_singleton hreachs hstep

theorem finiteHorizon_bound_reachStateTrace
    (hh : h.length ≤ k) (hr : InfoModel.ReachStateTrace M h ss) :
    ss.length ≤ k + 1 := by
  simpa [reachStateTrace_length_relation (hr := hr)] using Nat.succ_le_succ hh

/-- `FiniteHorizon` bounds any reachable state-trace witness. -/
theorem finiteHorizon_from_reachStateTrace
    (hH : M.FiniteHorizon k)
    (hr : InfoModel.ReachStateTrace M h ss) :
    h.length ≤ k := by
  rcases reachStateTrace_to_reachBy (hr := hr) with ⟨s, _, hs⟩
  exact hH h s hs

end InfoModel
end GameTheory
