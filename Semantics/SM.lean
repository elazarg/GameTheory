/-! # Pointed labeled state machine

A generic state machine with label type `α`, state type `σ`, an initial state,
and a relational step function. This is domain-agnostic — no game theory,
no players, no observations. -/

set_option autoImplicit false

namespace Semantics

/-- Pointed labeled state machine: initial state + relational step. -/
structure SM (α σ : Type) where
  /-- Initial state. -/
  init : σ
  /-- Labeled transition relation: `step a s t` means label `a` takes state `s` to `t`. -/
  step : α → σ → σ → Prop

namespace SM

variable {α σ : Type}

/-- Reachability witness carrying visited states (includes init). -/
inductive ReachStateTrace (M : SM α σ) : List σ → Prop
  | nil : ReachStateTrace M [M.init]
  | snoc {ss : List σ} {s t : σ} {a : α} :
      ReachStateTrace M ss →
      ss.getLast? = some s →
      M.step a s t →
      ReachStateTrace M (ss ++ [t])

/-- Reachability witness carrying labels and visited states. -/
inductive ReachActionTrace (M : SM α σ) :
    List α → List σ → Prop
  | nil : ReachActionTrace M [] [M.init]
  | snoc
      {ha : List α}
      {ss : List σ} {s t : σ} {a : α} :
      ReachActionTrace M ha ss →
      ss.getLast? = some s →
      M.step a s t →
      ReachActionTrace M (ha ++ [a]) (ss ++ [t])

theorem ReachActionTrace.length_states_eq_succ_actions
    {M : SM α σ} {ha : List α} {ss : List σ}
    (h : ReachActionTrace M ha ss) :
    ss.length = ha.length + 1 := by
  induction h with
  | nil => simp
  | snoc _ _ _ ih => simp [List.length_append, ih, Nat.add_comm]

/-- Forgetting labels from a label/state witness yields a state-trace witness. -/
theorem ReachActionTrace.toReachStateTrace
    {M : SM α σ} {ha : List α} {ss : List σ}
    (h : ReachActionTrace M ha ss) :
    ReachStateTrace M ss := by
  induction h with
  | nil => exact .nil
  | snoc _ hlast hstep ih => exact .snoc ih hlast hstep

end SM
end Semantics
