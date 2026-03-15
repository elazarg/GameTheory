import Math.PMFProduct
import GameTheory.Languages.MAID.SOS
import GameTheory.Theorems.Kuhn.ObsModel

/-!
# GameTheory.Languages.MAID.CompileObs

Compilation of MAID frontier semantics into the `ObsModel` layer.

The compiled `ObsModel` treats each frontier step as a stochastic transition:
chance nodes sample from their CPDs, decision nodes are determined by the
player actions, and utility nodes take their deterministic values. The combined
effect is a `PMF` over successor frontier configurations.

## Main definitions

- `compileObsModel S sem` : the observation model for MAID frontier semantics
-/

namespace MAID

open GameTheory Math.PMFProduct Math.ProbabilityMassFunction

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

/-- Stochastic frontier step: given a frontier configuration and joint player
actions, produce a distribution over successor configurations.

This resolves the nondeterminism in the native SOS: chance nodes sample from
their CPDs, decision nodes read from the action profile, and utility nodes
are set deterministically. The result is a product of independent chance-node
CPDs over frontier values, pushed forward through `extendFrontier`. -/
noncomputable def frontierStepPMF (S : Struct Player n) (sem : Sem S)
    (cfg : FrontierCfg S)
    (acts : ∀ p : Player, Option (FrontierAct S p)) :
    PMF (FrontierCfg S) :=
  pushforward (pmfPi (nodeDistrib S sem cfg acts)) (extendFrontier S cfg)

/-- Compile MAID frontier semantics into the observation model layer.

- **States**: frontier configurations (`FrontierCfg S`)
- **Players**: `Player`
- **Observations**: frontier infosets for each player (`List (Infoset S p)`)
- **Actions**: optional frontier acts per player (constant across observations)
- **Step**: stochastic resolution of one frontier assignment via `frontierStepPMF`
-/
noncomputable def compileObsModel (S : Struct Player n) (sem : Sem S) :
    ObsModel Player (FrontierCfg S)
      (fun p => List (Infoset S p))
      (fun (p : Player) (_ : List (Infoset S p)) => Option (FrontierAct S p)) where
  infoState := fun _ => InfoStateSpec.list _
  observe := fun p cfg => frontierInfosets S cfg p
  machine := {
    init := initialCfg S
    step := fun cfg acts => frontierStepPMF S sem cfg acts
  }

/-- The compiled ObsModel step is consistent with the native SOS:
the stochastic step assigns nonzero probability exactly to the states
reachable via the native `Step` relation. -/
theorem compileObsModel_step_consistent (S : Struct Player n) (sem : Sem S)
    (acts : ∀ p : Player, Option (FrontierAct S p))
    (cfg cfg' : FrontierCfg S) :
    (frontierStepPMF S sem cfg acts) cfg' ≠ 0 ↔ Step S sem acts cfg cfg' := by
  classical
  simp only [frontierStepPMF]
  constructor
  · -- Forward: nonzero pushforward → Step
    intro hne
    -- pushforward nonzero means ∃ vals with pmfPi nonzero and extendFrontier matches
    have hmem := (PMF.mem_support_iff _ _).mpr hne
    rw [show pushforward (pmfPi (nodeDistrib S sem cfg acts)) (extendFrontier S cfg) =
        PMF.map (extendFrontier S cfg) (pmfPi (nodeDistrib S sem cfg acts)) from rfl] at hmem
    rw [PMF.mem_support_map_iff] at hmem
    obtain ⟨vals, hvals_supp, hvals_eq⟩ := hmem
    rw [PMF.mem_support_iff] at hvals_supp
    subst hvals_eq
    -- pmfPi nonzero means all factors nonzero
    rw [pmfPi_apply] at hvals_supp
    have hprod_ne := (Finset.prod_ne_zero_iff (M₀ := ENNReal)).mp hvals_supp
    have hallowed : ∀ nd : ↥(frontier S cfg), FrontierValueAllowed S sem cfg acts nd (vals nd) := by
      intro nd
      exact hprod_ne nd (Finset.mem_univ nd)
    exact Step.mk hallowed
  · -- Backward: Step → nonzero pushforward
    intro hstep
    match hstep with
    | Step.mk (vals := vals) hallowed =>
      -- hallowed says each nodeDistrib factor is nonzero
      -- Need: pushforward pmfPi extendFrontier is nonzero
      have hmem : extendFrontier S cfg vals ∈
          (PMF.map (extendFrontier S cfg) (pmfPi (nodeDistrib S sem cfg acts))).support := by
        rw [PMF.mem_support_map_iff]
        refine ⟨_, ?_, rfl⟩
        rw [PMF.mem_support_iff, pmfPi_apply]
        exact (Finset.prod_ne_zero_iff (M₀ := ENNReal)).mpr (fun nd _ => hallowed nd)
      rw [show pushforward (pmfPi (nodeDistrib S sem cfg acts)) (extendFrontier S cfg) =
          PMF.map (extendFrontier S cfg) (pmfPi (nodeDistrib S sem cfg acts)) from rfl]
      exact (PMF.mem_support_iff _ _).mp hmem

/-- Core MAID compilation with the identity info-state model.

Unlike `compileObsModel` which uses the list-backed `InfoStateSpec.list`
representation via `ObsModel`, this compilation uses the identity info-state
core where the carrier is the observation type itself. This allows direct
application of `ObsModelCore`-level Kuhn theorems without going through the
`ObsModel` compatibility layer.

**Caveat**: The action type `Option (FrontierAct S p)` is non-trivial even when
player `p` has no active decision nodes. This means
`NoNontrivialInfoStateRepeat` can fail (the empty observation `[]` can repeat
with nontrivial action space). For the B→M direction under `PerfectRecall`,
use `compileObsCoreModelPR` instead, which uses the refined observation type
`Option (Infoset S p)`. -/
noncomputable def compileObsCoreModel (S : Struct Player n) (sem : Sem S) :
    ObsModelCore Player (FrontierCfg S)
      (fun p => List (Infoset S p))
      (fun (p : Player) (_ : List (Infoset S p)) => Option (FrontierAct S p)) where
  infoState := fun _ => {
    Carrier := List _
    start := id
    push := fun _ o => o
    current := id
    current_start := by intro o; rfl
    current_push := by intro _ o; rfl
  }
  observe := fun p cfg => frontierInfosets S cfg p
  machine := {
    init := initialCfg S
    step := fun cfg acts => frontierStepPMF S sem cfg acts
  }

/-- The compiled `ObsModelCore` for a MAID. -/
noncomputable abbrev compiledCoreObs (S : Struct Player n) (sem : Sem S) :=
  compileObsCoreModel S sem

-- ============================================================================
-- Perfect-recall-refined compilation
-- ============================================================================

/-- Under `PerfectRecall`, the observation is the unique active infoset
(or `none` when inactive). This is the MAID analogue of EFG's `CompiledAct`. -/
def CompiledMAIDAct (S : Struct Player n) (p : Player) :
    Option (Infoset S p) → Type
  | none => PUnit
  | some I => Val S I.1.val

instance compiledMAIDActFintype (S : Struct Player n) (p : Player)
    (o : Option (Infoset S p)) : Fintype (CompiledMAIDAct S p o) := by
  cases o <;> dsimp [CompiledMAIDAct] <;> infer_instance

instance compiledMAIDActNonempty (S : Struct Player n) (p : Player)
    (o : Option (Infoset S p)) : Nonempty (CompiledMAIDAct S p o) := by
  cases o with
  | none => exact ⟨PUnit.unit⟩
  | some I => exact ⟨⟨0, S.dom_pos I.1.val⟩⟩

instance compiledMAIDActSubsingleton_none (S : Struct Player n) (p : Player) :
    Subsingleton (CompiledMAIDAct S p none) :=
  inferInstanceAs (Subsingleton PUnit)

/-- Extract the unique active infoset from a frontier configuration.

Under `PerfectRecall`, at most one of player `p`'s decision nodes is enabled
at any frontier (because decision nodes are totally ordered by ancestry and
only a node whose parents are all assigned can be enabled). This function
extracts the head of `frontierInfosets` (if any). -/
noncomputable def frontierActiveInfoset (S : Struct Player n)
    (cfg : FrontierCfg S) (p : Player) : Option (Infoset S p) :=
  (frontierInfosets S cfg p).head?

/-- Stochastic frontier step for the perfect-recall-refined compilation.

Each player's action at observation `some I` is a value `Val S I.1.val`
for the decision node `I.1`. At observation `none`, the action is `PUnit`
(trivial). The step converts these back to the `Option (FrontierAct S p)`
format expected by `frontierStepPMF`. -/
noncomputable def frontierStepPMF_PR (S : Struct Player n) (sem : Sem S)
    (cfg : FrontierCfg S)
    (acts : ∀ p : Player, CompiledMAIDAct S p (frontierActiveInfoset S cfg p)) :
    PMF (FrontierCfg S) :=
  let rawActs : ∀ p : Player, Option (FrontierAct S p) := fun p =>
    match h : frontierActiveInfoset S cfg p with
    | none => none
    | some I =>
        some (fun d =>
          if hd : d = I.1 then
            some (hd ▸ (show CompiledMAIDAct S p (some I) from h ▸ acts p))
          else none)
  frontierStepPMF S sem cfg rawActs

/-- Core MAID compilation refined for `PerfectRecall`.

Observations are `Option (Infoset S p)` (at most one active infoset under
perfect recall). Actions are `CompiledMAIDAct S p` — trivial when inactive,
`Val S d.val` when acting at decision node `d`. This ensures
`NoNontrivialInfoStateRepeat` holds, enabling the B→M direction of Kuhn's
theorem. -/
noncomputable def compileObsCoreModelPR (S : Struct Player n) (sem : Sem S) :
    ObsModelCore Player (FrontierCfg S)
      (fun p => Option (Infoset S p))
      (CompiledMAIDAct S) where
  infoState := fun _ => {
    Carrier := Option _
    start := id
    push := fun _ o => o
    current := id
    current_start := by intro o; rfl
    current_push := by intro _ o; rfl
  }
  observe := fun p cfg => frontierActiveInfoset S cfg p
  machine := {
    init := initialCfg S
    step := fun cfg acts => frontierStepPMF_PR S sem cfg acts
  }

-- ============================================================================
-- Profile lift/descend between native MAID and compiled PR model
-- ============================================================================

section ProfileLiftDescend

variable (S : Struct Player n) (sem : Sem S)

/-- Lift a native pure strategy to a compiled PR local strategy.
The compiled PR model uses identity info state, so `InfoState p = Option (Infoset S p)`
and `currentObs = id`. At `some I`, the action type is `Val S I.1.val`;
at `none`, it is `PUnit`. -/
def liftPureStrategy {p : Player} (σ : PureStrategy S p) :
    (compileObsCoreModelPR S sem).LocalStrategy p :=
  fun v => match v with
    | none => PUnit.unit
    | some I => σ I

/-- Lift a native pure policy to a compiled PR pure profile. -/
def liftPureProfile (π : PurePolicy S) :
    ObsModelCore.PureProfile (compileObsCoreModelPR S sem) :=
  fun p => liftPureStrategy S sem (π p)

/-- Descend a compiled PR local strategy to a native pure strategy. -/
def descendPureStrategy (σ' : (compileObsCoreModelPR S sem).LocalStrategy p) :
    PureStrategy S p :=
  fun I => σ' (some I)

/-- Descend a compiled PR pure profile to a native pure policy. -/
def descendPureProfile (π' : ObsModelCore.PureProfile (compileObsCoreModelPR S sem)) :
    PurePolicy S :=
  fun p => descendPureStrategy S sem (π' p)

/-- Round-trip: descend ∘ lift = id for pure strategies. -/
theorem descend_lift_pureStrategy (σ : PureStrategy S p) :
    descendPureStrategy S sem (liftPureStrategy S sem σ) = σ := by
  funext I; rfl

/-- Round-trip: descend ∘ lift = id for pure policies. -/
theorem descend_lift_pureProfile (π : PurePolicy S) :
    descendPureProfile S sem (liftPureProfile S sem π) = π := by
  funext p I; rfl

/-- Lift a native policy to a compiled PR behavioral profile. -/
noncomputable def liftBehavioralProfile (pol : Policy S) :
    ObsModelCore.BehavioralProfile (compileObsCoreModelPR S sem) :=
  fun p v => match v with
    | none => PMF.pure PUnit.unit
    | some I => pol p I

/-- Descend a compiled PR behavioral profile to a native policy. -/
noncomputable def descendBehavioralProfile
    (β : ObsModelCore.BehavioralProfile (compileObsCoreModelPR S sem)) :
    Policy S :=
  fun p I => β p (some I)

/-- Round-trip: descend ∘ lift = id for behavioral profiles. -/
theorem descend_lift_behavioralProfile (pol : Policy S) :
    descendBehavioralProfile S sem (liftBehavioralProfile S sem pol) = pol := by
  funext p I; rfl

/-- Lift a native mixed profile to compiled PR per-player mixed strategies. -/
noncomputable def liftMixedProfile (μ : ∀ p, PMF (PureStrategy S p)) :
    ∀ p, PMF ((compileObsCoreModelPR S sem).LocalStrategy p) :=
  fun p => (μ p).map (liftPureStrategy S sem)

end ProfileLiftDescend

end MAID
