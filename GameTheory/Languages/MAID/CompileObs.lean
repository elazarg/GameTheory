import GameTheory.Languages.MAID.SOS
import GameTheory.Theorems.Kuhn.ObsModel
import Math.PMFProduct

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

end MAID
