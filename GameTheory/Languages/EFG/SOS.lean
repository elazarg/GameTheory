import GameTheory.Languages.EFG.Compile
import GameTheory.Model.Simulation

namespace GameTheory.EFG

open _root_.EFG

/-- Compile a syntax-level EFG history step to the joint action used by the
compiled state machine. Chance moves become all-player inactivity; decision
moves activate only the acting player. -/
def jointActionOfHistoryStep
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome) :
    _root_.EFG.HistoryStep S →
      (compileInfoOn (S := S) (Outcome := Outcome) t).JointAction
  | .chance _ _ => fun _ => none
  | .action p I act => Function.update (fun _ => none) p (some (Sigma.mk I act))

@[simp] theorem jointActionOfHistoryStep_chance
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    (k : Nat) (b : Fin k) (i : S.Player) :
    jointActionOfHistoryStep t (.chance k b) i = none := rfl

@[simp] theorem jointActionOfHistoryStep_action_self
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    {p : S.Player} (I : S.Infoset p) (act : S.Act I) :
    jointActionOfHistoryStep t (.action p I act) p = some (Sigma.mk I act) := by
  simp [jointActionOfHistoryStep]

@[simp] theorem jointActionOfHistoryStep_action_other
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    {p q : S.Player} (I : S.Infoset p) (act : S.Act I)
    (hq : q ≠ p) :
    jointActionOfHistoryStep t (.action p I act) q = none := by
  simp [jointActionOfHistoryStep, Function.update, hq]

/-- Every syntax-level one-step EFG move is a valid step of the compiled latent
state machine under the corresponding compiled joint action. -/
theorem historyStepStep_implies_compiled_step
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    {ℓ : _root_.EFG.HistoryStep S}
    {src dst : _root_.EFG.GameTree S Outcome}
    (h : _root_.EFG.HistoryStepStep (S := S) (Outcome := Outcome) ℓ src dst) :
    (compileInfoOn (S := S) (Outcome := Outcome) t).step
      (jointActionOfHistoryStep t ℓ) src dst := by
  cases ℓ with
  | chance k b =>
      rcases h with ⟨μ, hk, next, rfl, rfl⟩
      exact ⟨by intro i; rfl, ⟨b, rfl⟩⟩
  | action p I act =>
      rcases h with ⟨next, rfl, rfl⟩
      refine ⟨act, ?_, ?_, rfl⟩
      · simp [jointActionOfHistoryStep]
      · intro q hq
        simp [jointActionOfHistoryStep, Function.update, hq]

/-- Every compiled one-step transition comes from some syntax-level EFG history
step. Chance branch choices are recovered from the reached successor state. -/
theorem compiled_step_implies_exists_historyStep
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    {a : (compileInfoOn (S := S) (Outcome := Outcome) t).JointAction}
    {src dst : _root_.EFG.GameTree S Outcome}
    (h : (compileInfoOn (S := S) (Outcome := Outcome) t).step a src dst) :
    ∃ ℓ : _root_.EFG.HistoryStep S,
      _root_.EFG.HistoryStepStep (S := S) (Outcome := Outcome) ℓ src dst := by
  cases src with
  | terminal z =>
      cases h
  | chance k μ hk next =>
      rcases h with ⟨_, b, rfl⟩
      exact ⟨.chance k b, ⟨μ, hk, next, rfl, rfl⟩⟩
  | @decision p I next =>
      rcases h with ⟨act, _, _, rfl⟩
      exact ⟨.action p I act, ⟨next, rfl, rfl⟩⟩

/-- Syntax-level reachability yields compiled reachability along the compiled
joint-action trace. -/
theorem reachBy_implies_compiled
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    {h : List (_root_.EFG.HistoryStep S)}
    {src dst : _root_.EFG.GameTree S Outcome}
    (hr : _root_.EFG.ReachBy h src dst) :
    Semantics.Transition.ReachBy (compileInfoOn (S := S) (Outcome := Outcome) t).step
      (h.map (jointActionOfHistoryStep t)) src dst := by
  induction hr with
  | nil s =>
      exact Semantics.Transition.ReachBy.nil s
  | @cons a rest s u v hstep hreach ih =>
      simpa [List.map] using
        Semantics.Transition.ReachBy.cons
          (historyStepStep_implies_compiled_step t hstep) ih

/-- Compiled reachability is equivalent to existence of some syntax-level EFG
history reaching the same destination. The compiled action trace erases chance
branch labels, so the converse is existential rather than pointwise. -/
theorem compiled_reach_iff_exists_history
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    {src dst : _root_.EFG.GameTree S Outcome} :
    (∃ ha,
      Semantics.Transition.ReachBy (compileInfoOn (S := S) (Outcome := Outcome) t).step
        ha src dst)
      ↔
    (∃ h : List (_root_.EFG.HistoryStep S), _root_.EFG.ReachBy h src dst) := by
  constructor
  · rintro ⟨ha, hr⟩
    induction hr with
    | nil s =>
        exact ⟨[], Semantics.Transition.ReachBy.nil s⟩
    | @cons a rest s u v hstep hreach ih =>
        rcases compiled_step_implies_exists_historyStep t hstep with ⟨ℓ, hℓ⟩
        rcases ih with ⟨h, hh⟩
        exact ⟨ℓ :: h, Semantics.Transition.ReachBy.cons hℓ hh⟩
  · rintro ⟨h, hr⟩
    exact ⟨h.map (jointActionOfHistoryStep t), reachBy_implies_compiled t hr⟩

/-- Honest semantic contract for the current EFG compilation.

This is a homomorphic simulation, not a bisimulation on source labels:
player action steps are preserved exactly, while chance branch labels are
mapped to the compiled joint action alphabet by `jointActionOfHistoryStep`.
The state and observation components are preserved definitionally. -/
def nativeInfoHomSimulation
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome) :
    GameTheory.NativeInfoHomSimulation
      (_root_.EFG.HistoryStepStep (S := S) (Outcome := Outcome))
      t
      (compileInfoOn (S := S) (Outcome := Outcome) t)
      (fun _ => PUnit.unit)
      (obsOfState (S := S) (Outcome := Outcome)) where
  stateMap := id
  labelMap := jointActionOfHistoryStep t
  init := rfl
  step := by
    intro ℓ src dst h
    exact historyStepStep_implies_compiled_step t h
  publicView_eq := by
    intro s
    rfl
  observe_eq := by
    intro i s
    rfl

end GameTheory.EFG
