import GameTheory.Languages.MAID.Compile

/-!
# GameTheory.Theorems.MAID

Target-side reduction lemmas for compiled MAIDs.

This file packages the structural equivalence between native frontier semantics
and the compiled `InfoModel` presentation so later theorem ports can ignore the
surface syntax.
-/

namespace GameTheory.Theorems.MAID

open _root_.MAID

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

/-- The compiled MAID machine has exactly the native frontier step relation. -/
theorem step_iff
    (S : Struct Player n) (sem : Sem S)
    (a : ∀ p : Player, Option (FrontierAct S p))
    (src dst : FrontierCfg S) :
    (compileLSM S sem).step a src dst ↔ Step S sem a src dst :=
  compile_step_iff S sem a src dst

/-- Reachability in the compiled machine is exactly native frontier reachability. -/
theorem reach_iff
    (S : Struct Player n) (sem : Sem S)
    (ha : List (∀ p : Player, Option (FrontierAct S p)))
    (src dst : FrontierCfg S) :
    Semantics.Transition.ReachBy (compileLSM S sem |>.stepExists) ha src dst ↔
      ReachBy S sem ha src dst :=
  compile_reach_iff S sem ha src dst

/-- The compiled information model exposes the native frontier list. -/
theorem publicView_eq
    (S : Struct Player n) (sem : Sem S)
    (cfg : FrontierCfg S) :
    (compileInfoOn S sem).publicView cfg = frontierList S cfg :=
  compile_publicView_eq_frontier S sem cfg

/-- The compiled information model exposes the native frontier infosets. -/
theorem observe_eq
    (S : Struct Player n) (sem : Sem S)
    (p : Player) (cfg : FrontierCfg S) :
    (compileInfoOn S sem).observe p cfg = frontierInfosets S cfg p :=
  compile_observe_eq_frontierInfosets S sem p cfg

/-- Placeholder reduction target for future theorem ports over compiled MAIDs. -/
def KuhnReductionTarget
    (S : Struct Player n) (sem : Sem S) : Prop :=
  let _ := sem
  ∀ _ : FrontierCfg S, True

end GameTheory.Theorems.MAID
