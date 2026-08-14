/-
# General typed, site-local MAID frontier semantics

Syntax stores neither finite-carrier capabilities nor an execution order.
Native policies are indexed by decision site and receive only that site's
observed-parent configuration. Evaluation resolves the entire current minimal
frontier by one dependent finite product. The public laws validate this
representation and its exact compiled-EFG semantics.
-/

import GameTheory.Probability.FinDist
import GameTheoryMath.DAG

noncomputable section

namespace GameTheory.Languages.MAID

open GameTheory.Probability

universe uPlayer uNode uValue

inductive NodeKind (Player : Type uPlayer)
  | chance
  | decision (owner : Player)
  deriving DecidableEq

/-- Typed causal diagram. Operational finite capabilities are deliberately not
stored here. -/
structure Structure (Player : Type uPlayer) (Node : Type uNode) where
  kind : Node → NodeKind Player
  parents : Node → Finset Node
  observedParents : Node → Finset Node
  Value : Node → Type uValue
  observed_sub : ∀ node, observedParents node ⊆ parents node
  observed_eq_of_chance : ∀ node, kind node = .chance →
    observedParents node = parents node
  acyclic : GameTheoryMath.DAG.Acyclic
    (fun first second => first ∈ parents second)

variable {Player : Type uPlayer} {Node : Type uNode}
variable (diagram : Structure Player Node)

def Assignment :=
  (node : Node) → diagram.Value node

def Config (nodes : Finset Node) :=
  (node : {node // node ∈ nodes}) → diagram.Value node.1

def Assignment.restrict (assignment : Assignment diagram)
    (nodes : Finset Node) : Config diagram nodes :=
  fun node => assignment node.1

def DecisionSite (owner : Player) :=
  {node : Node // diagram.kind node = .decision owner}

/-- One source owner's complete family of site-local behavioral rules. Sites
remain indexed by their source owner; they are not promoted to players. -/
abbrev OwnerPolicy (owner : Player) :=
  (site : DecisionSite diagram owner) →
    Config diagram (diagram.observedParents site.1) →
      FinDist (diagram.Value site.1)

/-- Behavioral policy is local by type: a decision-site rule receives only
that site's declared observation configuration. -/
abbrev Policy :=
  (owner : Player) → OwnerPolicy diagram owner

/-- Numeric semantics. Defaults initialize semantically inaccessible unresolved
coordinates; chance laws and utility are the actual mathematical content. -/
structure Semantics where
  defaultValue : (node : Node) → diagram.Value node
  chanceLaw : (node : Node) → diagram.kind node = .chance →
    Config diagram (diagram.parents node) → FinDist (diagram.Value node)
  utility : Player → Assignment diagram → ℝ

/-- A partial evaluation state carries the named predecessor-closure
certificate required by frontier evaluation. -/
structure FrontierState where
  resolved : Finset Node
  values : Assignment diagram
  parentClosed : ∀ node ∈ resolved, diagram.parents node ⊆ resolved

namespace FrontierState

variable {diagram}

def initial (semantics : Semantics diagram) : FrontierState diagram where
  resolved := ∅
  values := semantics.defaultValue
  parentClosed := by simp

@[reducible]
def IsComplete [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram) : Prop :=
  state.resolved = Finset.univ

/-- The unresolved nodes all of whose causal parents are already resolved. -/
def frontier [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram) : Finset Node :=
  Finset.univ.filter fun node =>
    node ∉ state.resolved ∧ diagram.parents node ⊆ state.resolved

theorem mem_frontier_iff [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram) (node : Node) :
    node ∈ state.frontier ↔
      node ∉ state.resolved ∧
        diagram.parents node ⊆ state.resolved := by
  simp [frontier]

theorem frontier_disjoint [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram) :
    Disjoint state.frontier state.resolved := by
  rw [Finset.disjoint_left]
  intro node hfrontier hresolved
  exact (state.mem_frontier_iff node).mp hfrontier |>.1 hresolved

theorem frontier_parents_resolved [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram) {node : Node}
    (hnode : node ∈ state.frontier) :
    diagram.parents node ⊆ state.resolved :=
  ((state.mem_frontier_iff node).mp hnode).2

/-- A finite acyclic evaluation never gets stuck before all nodes resolve. -/
theorem frontier_nonempty [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram)
    (hincomplete : ¬ state.IsComplete) :
    state.frontier.Nonempty := by
  have hunresolved : ∃ node, node ∉ state.resolved := by
    simpa [IsComplete, Finset.eq_univ_iff_forall] using hincomplete
  let wellFounded := diagram.acyclic.wellFounded
  let unresolved : Set Node := {node | node ∉ state.resolved}
  have hunresolvedSet : unresolved.Nonempty := hunresolved
  let minimal := wellFounded.min unresolved hunresolvedSet
  have hminimal : minimal ∉ state.resolved :=
    wellFounded.min_mem unresolved hunresolvedSet
  have hparents : diagram.parents minimal ⊆ state.resolved := by
    intro parent hparent
    by_contra hunresolvedParent
    exact wellFounded.not_lt_min unresolved hunresolvedParent hparent
  exact ⟨minimal,
    (state.mem_frontier_iff minimal).mpr ⟨hminimal, hparents⟩⟩

def configOf (state : FrontierState diagram) (nodes : Finset Node)
    (_hresolved : nodes ⊆ state.resolved) :
    Config diagram nodes :=
  Assignment.restrict diagram state.values nodes

end FrontierState

/-- Replace all coordinates in one frontier simultaneously. The sampled
coordinate retains the same node index, so no equality transport is needed. -/
def Assignment.resolve [DecidableEq Node]
    (assignment : Assignment diagram)
    (frontier : Finset Node)
    (draw : (node : {node // node ∈ frontier}) →
      diagram.Value node.1) :
    Assignment diagram :=
  fun node =>
    if hnode : node ∈ frontier
    then draw ⟨node, hnode⟩
    else assignment node

theorem Assignment.resolve_of_mem [DecidableEq Node]
    (assignment : Assignment diagram)
    (frontier : Finset Node)
    (draw : (node : {node // node ∈ frontier}) →
      diagram.Value node.1)
    {node : Node} (hnode : node ∈ frontier) :
    Assignment.resolve diagram assignment frontier draw node =
      draw ⟨node, hnode⟩ := by
  simp [Assignment.resolve, hnode]

theorem Assignment.resolve_of_notMem [DecidableEq Node]
    (assignment : Assignment diagram)
    (frontier : Finset Node)
    (draw : (node : {node // node ∈ frontier}) →
      diagram.Value node.1)
    {node : Node} (hnode : node ∉ frontier) :
    Assignment.resolve diagram assignment frontier draw node =
      assignment node := by
  simp [Assignment.resolve, hnode]

namespace FrontierState

variable {diagram}

@[reducible]
def extend [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram)
    (draw : (node : {node // node ∈ state.frontier}) →
      diagram.Value node.1) :
    FrontierState diagram where
  resolved := state.resolved ∪ state.frontier
  values := Assignment.resolve diagram state.values state.frontier draw
  parentClosed := by
    intro node hnode
    rcases Finset.mem_union.mp hnode with hold | hfrontier
    · exact fun parent hparent =>
        Finset.mem_union_left _ (state.parentClosed node hold hparent)
    · exact fun parent hparent =>
        Finset.mem_union_left _
          (state.frontier_parents_resolved hfrontier hparent)

theorem resolved_subset_extend [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram)
    (draw : (node : {node // node ∈ state.frontier}) →
      diagram.Value node.1) :
    state.resolved ⊆ (state.extend draw).resolved :=
  Finset.subset_union_left

theorem frontier_subset_extend [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram)
    (draw : (node : {node // node ∈ state.frontier}) →
      diagram.Value node.1) :
    state.frontier ⊆ (state.extend draw).resolved :=
  Finset.subset_union_right

theorem extend_value_of_frontier [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram)
    (draw : (node : {node // node ∈ state.frontier}) →
      diagram.Value node.1)
    (node : {node // node ∈ state.frontier}) :
    (state.extend draw).values node.1 = draw node := by
  simpa only [extend] using
    Assignment.resolve_of_mem diagram state.values state.frontier
      draw node.2

theorem resolved_ssubset_extend_of_incomplete
    [Fintype Node] [DecidableEq Node]
    (state : FrontierState diagram)
    (hincomplete : ¬ state.IsComplete)
    (draw : (node : {node // node ∈ state.frontier}) →
      diagram.Value node.1) :
    state.resolved ⊂ (state.extend draw).resolved := by
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨state.resolved_subset_extend draw, ?_⟩
  obtain ⟨node, hnode⟩ := state.frontier_nonempty hincomplete
  intro heq
  have hresolved : node ∈ state.resolved := by
    rw [heq]
    exact state.frontier_subset_extend draw hnode
  exact ((state.mem_frontier_iff node).mp hnode).1 hresolved

end FrontierState

def nodeLaw [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    (state : FrontierState diagram)
    (node : {node // node ∈ state.frontier}) :
    FinDist (diagram.Value node.1) := by
  have hparents : diagram.parents node.1 ⊆ state.resolved :=
    state.frontier_parents_resolved node.2
  match hkind : diagram.kind node.1 with
  | .chance =>
      exact semantics.chanceLaw node.1 hkind
        (state.configOf _ hparents)
  | .decision owner =>
      have hobserved :
          diagram.observedParents node.1 ⊆ state.resolved :=
        diagram.observed_sub node.1 |>.trans hparents
      exact policy owner ⟨node.1, hkind⟩
        (state.configOf _ hobserved)

def frontierLaw [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    (state : FrontierState diagram) :
    FinDist ((node : {node // node ∈ state.frontier}) →
      diagram.Value node.1) :=
  FinDist.pi fun node => nodeLaw diagram semantics policy state node

def step [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    (state : FrontierState diagram) :
    FinDist (FrontierState diagram) :=
  (frontierLaw diagram semantics policy state).map state.extend

def run [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram) :
    Nat → FrontierState diagram → FinDist (FrontierState diagram)
  | 0, state => FinDist.pure state
  | fuel + 1, state =>
      if state.IsComplete
      then FinDist.pure state
      else (step diagram semantics policy state).bind
        (run semantics policy fuel)

def CompletesWithin [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    (horizon : Nat) (state : FrontierState diagram) : Prop :=
  ∀ reached ∈ (run diagram semantics policy horizon state).support,
    reached.IsComplete

theorem eq_extend_of_mem_support_step
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    (state reached : FrontierState diagram)
    (hreached :
      reached ∈ (step diagram semantics policy state).support) :
    ∃ draw :
        (node : {node // node ∈ state.frontier}) →
          diagram.Value node.1,
      reached = state.extend draw := by
  rw [step, FinDist.support_map] at hreached
  obtain ⟨draw, _, rfl⟩ := hreached
  exact ⟨draw, rfl⟩

theorem run_of_complete [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    (fuel : Nat) (state : FrontierState diagram)
    (hcomplete : state.IsComplete) :
    run diagram semantics policy fuel state = FinDist.pure state := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [run, if_pos hcomplete]

/-- One step per node is a uniform completion bound. A frontier may resolve
several nodes, so the actual run can finish earlier. -/
theorem run_complete_of_remaining_le
    [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram)
    (fuel : Nat) (state : FrontierState diagram)
    (hbound :
      Fintype.card Node - state.resolved.card ≤ fuel) :
    ∀ reached ∈ (run diagram semantics policy fuel state).support,
      reached.IsComplete := by
  induction fuel generalizing state with
  | zero =>
      intro reached hreached
      have hcardLe :
          state.resolved.card ≤ Fintype.card Node :=
        Finset.card_le_univ state.resolved
      have hcard :
          state.resolved.card = Fintype.card Node := by
        omega
      have hcomplete : state.IsComplete :=
        state.resolved.card_eq_iff_eq_univ.mp hcard
      rw [run, FinDist.mem_support_pure] at hreached
      simpa [hreached] using hcomplete
  | succ fuel ih =>
      intro reached hreached
      by_cases hcomplete : state.IsComplete
      · rw [run, if_pos hcomplete,
          FinDist.mem_support_pure] at hreached
        simpa [hreached] using hcomplete
      · rw [run, if_neg hcomplete,
          FinDist.support_bind] at hreached
        obtain ⟨next, hnext⟩ := Set.mem_iUnion.mp hreached
        obtain ⟨hnextStep, hnextRun⟩ :=
          Set.mem_iUnion.mp hnext
        obtain ⟨draw, rfl⟩ :=
          eq_extend_of_mem_support_step
            diagram semantics policy state next hnextStep
        have hcardGrowth :
            state.resolved.card <
              (state.extend draw).resolved.card :=
          Finset.card_lt_card
            (state.resolved_ssubset_extend_of_incomplete
              hcomplete draw)
        have hstateCardLe :
            state.resolved.card ≤ Fintype.card Node :=
          Finset.card_le_univ state.resolved
        have hnextCardLe :
            (state.extend draw).resolved.card ≤
              Fintype.card Node :=
          Finset.card_le_univ (state.extend draw).resolved
        have hnextBound :
            Fintype.card Node -
                (state.extend draw).resolved.card ≤ fuel := by
          omega
        exact ih (state.extend draw) hnextBound reached hnextRun

theorem completesWithin_card [Fintype Node] [DecidableEq Node]
    (semantics : Semantics diagram) (policy : Policy diagram) :
    CompletesWithin diagram semantics policy (Fintype.card Node)
      (FrontierState.initial semantics) := by
  apply run_complete_of_remaining_le
  simp [FrontierState.initial]

end GameTheory.Languages.MAID

