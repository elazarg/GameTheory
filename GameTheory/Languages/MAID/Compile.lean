import GameTheory.Languages.MAID.Syntax
import GameTheory.Languages.MAID.SOS
import GameTheory.Model.InfoGame

/-!
# GameTheory.Languages.MAID.Compile

Compilation of MAID frontier semantics into the generic `LSM`/`InfoModel`
layers.

The compiled state is exactly the native frontier configuration. A compiled step
is exactly one frontier assignment step of the native SOS semantics.
-/

namespace MAID

open GameTheory

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

/-- The MAID frontier SOS already has the right shape for the latent-state
machine layer, so compilation is structural. -/
def compileLSM (S : Struct Player n) (sem : Sem S) : GameTheory.LSM Player where
  State := FrontierCfg S
  Act := FrontierAct S
  init := initialCfg S
  step := Step S sem

/-- Publicly visible frontier information in the compiled MAID semantics. -/
abbrev PublicObs := List (Fin n)

/-- Compile MAID visibility into the generic `InfoModel` layer. Public
visibility is the current frontier in topological order; player-local
visibility is the list of currently enabled infosets for that player. -/
noncomputable def compileInfoOn (S : Struct Player n) (sem : Sem S) :
    GameTheory.InfoModel (compileLSM S sem) where
  Public := PublicObs
  publicView := frontierList S
  Obs := fun p => List (Infoset S p)
  observe := fun p cfg => frontierInfosets S cfg p

/-- A compiled MAID step is definitionally a frontier SOS step. -/
theorem compile_step_iff
    (S : Struct Player n) (sem : Sem S)
    (a : ∀ p : Player, Option (FrontierAct S p))
    (src dst : FrontierCfg S) :
    (compileLSM S sem).step a src dst ↔ Step S sem a src dst := by
  rfl

/-- Reachability in the compiled machine is definitionally the same as native
frontier reachability. -/
theorem compile_reach_iff
    (S : Struct Player n) (sem : Sem S)
    (ha : List (∀ p : Player, Option (FrontierAct S p)))
    (src dst : FrontierCfg S) :
    Semantics.Transition.ReachBy (compileLSM S sem |>.stepExists) ha src dst ↔
      ReachBy S sem ha src dst := by
  rfl

/-- The compiled public view is exactly the native frontier list. -/
theorem compile_publicView_eq_frontier
    (S : Struct Player n) (sem : Sem S)
    (cfg : FrontierCfg S) :
    (compileInfoOn S sem).publicView cfg = frontierList S cfg := by
  rfl

/-- The compiled player observation is exactly the native frontier infoset list. -/
theorem compile_observe_eq_frontierInfosets
    (S : Struct Player n) (sem : Sem S)
    (p : Player) (cfg : FrontierCfg S) :
    (compileInfoOn S sem).observe p cfg = frontierInfosets S cfg p := by
  rfl

/-- Build a common-knowledge utility layer over the compiled MAID semantics. -/
def compileControlUtility (S : Struct Player n) (sem : Sem S)
    (u : ∀ p : Player, List (List (Infoset S p)) → ℝ) :
    GameTheory.ControlModel (compileLSM S sem) (compileInfoOn S sem) where
  control := fun p => GameTheory.ControlSpec.utility (u p)

/-- Build a common-knowledge behavioral layer over the compiled MAID
semantics. -/
def compileControlBehavior (S : Struct Player n) (sem : Sem S)
    (β : ∀ p : Player,
      List (List (Infoset S p)) → PMF (Option (FrontierAct S p))) :
    GameTheory.ControlModel (compileLSM S sem) (compileInfoOn S sem) where
  control := fun p => GameTheory.ControlSpec.behavior (β p)

/-- Compile a MAID together with common-knowledge utility specifications into
the game-level `InfoGame` target. -/
noncomputable def compileInfoGameUtility (S : Struct Player n) (sem : Sem S)
    (u : ∀ p : Player, List (List (Infoset S p)) → ℝ) :
    GameTheory.InfoGame (ι := Player) :=
  .ofControlModel <| compileControlUtility S sem u

/-- Compile a MAID together with common-knowledge behavioral specifications
into the game-level `InfoGame` target. -/
noncomputable def compileInfoGameBehavior (S : Struct Player n) (sem : Sem S)
    (β : ∀ p : Player,
      List (List (Infoset S p)) → PMF (Option (FrontierAct S p))) :
    GameTheory.InfoGame (ι := Player) :=
  .ofControlModel <| compileControlBehavior S sem β

end MAID
