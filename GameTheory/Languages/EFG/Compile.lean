import GameTheory.Model.SemanticForm
import GameTheory.Languages.EFG.Syntax

namespace GameTheory
namespace Languages
namespace EFG

open _root_.EFG

/-- EFG controller action alphabet at player `i`: infoset + local action. -/
abbrev CtrlAct (S : _root_.EFG.InfoStructure) (i : S.Player) : Type :=
  Sigma (fun I : S.Infoset i => S.Act I)

/-- Compile EFG transition semantics to the generic LSM layer.
Joint actions are ignored because EFG step labels already carry the realized move. -/
def compileLSM {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome) : GameTheory.LSM S.Player where
  Label := _root_.EFG.HistoryStep S
  State := _root_.EFG.GameTree S Outcome
  Act := CtrlAct S
  init := t
  step := fun ℓ _ s s' => _root_.EFG.HistoryStepStep (S := S) (Outcome := Outcome) ℓ s s'

/-- Local observation token extracted from a state for player `i`. -/
def obsOfState {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (i : S.Player) : _root_.EFG.GameTree S Outcome → Option (S.Infoset i)
  | .decision (p := p) I _ =>
      if h : p = i then
        by
          subst h
          exact some I
      else none
  | _ => none

/-- Compile EFG information to the generic `InfoModel` layer. -/
def compileInfoOn {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome) :
    GameTheory.InfoModel (compileLSM (S := S) (Outcome := Outcome) t) where
  Obs := fun i => Option (S.Infoset i)
  infoSetoid := fun i =>
    ⟨fun s₁ s₂ => obsOfState (S := S) (Outcome := Outcome) i s₁ =
        obsOfState (S := S) (Outcome := Outcome) i s₂,
      ⟨by intro s; rfl,
       by intro s t h; simpa [eq_comm] using h,
       by intro s t u hst htu; exact hst.trans htu⟩⟩
  project := fun i h =>
    (_root_.EFG.playerHistory S i h).map (fun a => Sum.inr (some a))

/-- Build a pure-utility control model from local utility functionals. -/
def compileControlUtility {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    (u : ∀ i : S.Player,
      List (Option (S.Infoset i) ⊕ Option (CtrlAct S i)) → ℝ) :
    GameTheory.ControlModel (compileLSM (S := S) (Outcome := Outcome) t)
      (compileInfoOn (S := S) (Outcome := Outcome) t) where
  control := fun i => GameTheory.ControlSpec.utility (u i)

/-- Build a pure-behavior control model from local public behavior laws. -/
def compileControlBehavior {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    (β : ∀ i : S.Player,
      _root_.EFG.HistoryStep S → Option (S.Infoset i) → PMF (Option (CtrlAct S i))) :
    GameTheory.ControlModel (compileLSM (S := S) (Outcome := Outcome) t)
      (compileInfoOn (S := S) (Outcome := Outcome) t) where
  control := fun i => GameTheory.ControlSpec.behavior (β i)

/-- Reachability in EFG syntax is equivalent to reachability under compiled machine
action-erased dynamics. -/
theorem reachBy_iff_compiled
    {S : _root_.EFG.InfoStructure} {Outcome : Type}
    (t : _root_.EFG.GameTree S Outcome)
    (h : List (_root_.EFG.HistoryStep S))
    (src dst : _root_.EFG.GameTree S Outcome) :
    _root_.EFG.ReachBy h src dst ↔
      Semantics.Transition.ReachBy (compileLSM (S := S) (Outcome := Outcome) t |>.stepExists)
        h src dst := by
  constructor
  · intro hr
    induction hr with
    | nil s =>
      exact Semantics.Transition.ReachBy.nil s
    | @cons a rest s u v hsu huv ih =>
        refine Semantics.Transition.ReachBy.cons ?_ ih
        exact ⟨fun _ => none, hsu⟩
  · intro hr
    induction hr with
    | nil s =>
        exact Semantics.Transition.ReachBy.nil s
    | @cons a rest s u v hsu huv ih =>
        rcases hsu with ⟨_, hstep⟩
        exact Semantics.Transition.ReachBy.cons hstep ih

end EFG
end Languages
end GameTheory
