/-! # Latent-state machine (multi-agent)

A multi-agent state machine with per-player action types, an initial state,
and a relational step function. This is the foundational type for all
sequential game models (InfoModel, ObsModel, EFG, etc.).

Also defines `ReachStateTrace` and `ReachActionTrace` (reachability witnesses
via state/action sequences) and `projectActions` (player-local action extraction).
These depend only on `LSM`, not on any observation or information model. -/

set_option autoImplicit false

namespace GameTheory

/-- Multi-agent latent-state machine with per-player actions. -/
structure LSM (ι : Type) where
  State : Type
  Act : ι → Type
  init : State
  step : (∀ i, Option (Act i)) → State → State → Prop

/-- Joint (possibly inactive) action profile. -/
abbrev JointAction {ι : Type} (M : LSM ι) : Type :=
  ∀ i, Option (M.Act i)

namespace LSM

variable {ι : Type}

/-- Action-erased one-step relation. -/
def stepExists (M : LSM ι) : JointAction M → M.State → M.State → Prop :=
  M.step

end LSM

/-- Reachability witness carrying visited states (states include init). -/
inductive ReachStateTrace {ι : Type} (M : LSM ι) : List M.State → Prop
  | nil : ReachStateTrace M [M.init]
  | snoc {ss : List M.State} {s t : M.State} {a : JointAction M} :
      ReachStateTrace M ss →
      ss.getLast? = some s →
      M.step a s t →
      ReachStateTrace M (ss ++ [t])

/-- Reachability witness carrying joint actions and visited states. -/
inductive ReachActionTrace {ι : Type} (M : LSM ι) :
    List (JointAction M) → List M.State → Prop
  | nil : ReachActionTrace M [] [M.init]
  | snoc
      {ha : List (JointAction M)}
      {ss : List M.State} {s t : M.State} {a : JointAction M} :
      ReachActionTrace M ha ss →
      ss.getLast? = some s →
      M.step a s t →
      ReachActionTrace M (ha ++ [a]) (ss ++ [t])

theorem ReachActionTrace.length_states_eq_succ_actions
    {ι : Type} {M : LSM ι}
    {ha : List (JointAction M)}
    {ss : List M.State}
    (h : ReachActionTrace M ha ss) :
    ss.length = ha.length + 1 := by
  induction h with
  | nil =>
      simp
  | snoc _ _ _ ih =>
      simp [List.length_append, ih, Nat.add_comm]

/-- Forgetting actions from an action/state witness yields a state-trace witness. -/
theorem ReachActionTrace.toReachStateTrace
    {ι : Type} {M : LSM ι}
    {ha : List (JointAction M)}
    {ss : List M.State} (h : ReachActionTrace M ha ss) :
    ReachStateTrace M ss := by
  induction h with
  | nil => exact .nil
  | snoc _ hlast hstep ih =>
      exact .snoc ih hlast hstep

/-- Player-local projected own-action trace from an action-annotated history. -/
def projectActions {ι : Type} {M : LSM ι} (i : ι) (ha : List (JointAction M)) :
    List (Option (M.Act i)) :=
  ha.map (fun a => a i)

end GameTheory
