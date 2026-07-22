/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.DAG
import GameTheory.Languages.MAID.Prefix
import Math.FiniteProbabilityMassFunction

/-!
# Sparse Open-Game DAGs as Bayesian Networks

A local causal law assigns every sparse DAG node a finite stochastic kernel
from its typed parent configuration. Evaluation is delegated to the existing
MAID Bayesian-network factorization, rather than introducing a second
stochastic DAG evaluator.

All nodes in the backend `MAID.Struct` are marked as chance nodes because this
module concerns joint-law construction, not strategic ownership. A later game
layer may designate some kernels as fixed chance mechanisms and others as
behavioral decision policies. The deterministic embedding proves that pure
`ShapeDAG` contingent plans induce exactly the point mass at their existing
well-founded realization.

The finite-carrier constraints are inherited from `MAID.Struct`; they are not
requirements of deterministic `ShapeDAG` itself.
-/

noncomputable section

namespace OpenGames.ShapeDAG.Causal

variable {n : Nat}

/-- Local finite stochastic kernels indexed by sparse-DAG nodes. -/
abbrev LocalKernel (D : DecisionDAG n) (A : Fin n → Type) :=
  ∀ i, History D A i → Math.FinPMF (A i)

/-- The natural topological certificate implies ordinary graph acyclicity. -/
theorem parents_acyclic (D : DecisionDAG n) :
    Math.DAG.Acyclic (fun parent child => parent ∈ D.parents child) := by
  intro i hii
  exact (Nat.lt_irrefl i.val) (D.ancestor_lt hii)

/-- The typed Bayesian-network structure underlying a sparse decision DAG.

Every node is marked `chance` here: strategic/fixed status belongs to a layer
that chooses which local kernels may deviate, while the joint-law evaluator is
the same in either case. -/
def maidStruct (D : DecisionDAG n) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] : MAID.Struct Unit n where
  kind _ := .chance
  parents := D.parents
  obsParents := D.parents
  Val := A
  instFintype i := inferInstanceAs (Fintype (A i))
  instDecidableEq i := inferInstanceAs (DecidableEq (A i))
  instInhabited i := inferInstanceAs (Inhabited (A i))
  obs_sub _ := Finset.Subset.rfl
  obs_eq_nondec _ _ := rfl
  utility_unique := by
    intro nd player h
    cases h
  acyclic := parents_acyclic D

/-- The sparse node numbering is a natural MAID topological order. -/
theorem maidStruct_naturalOrder (D : DecisionDAG n) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] : (maidStruct D A).NaturalOrder := by
  intro node parent hparent
  exact D.parent_lt hparent

/-- Interpret finite local kernels as the chance CPDs of the MAID backend. -/
def sem (D : DecisionDAG n) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (κ : LocalKernel D A) :
    MAID.Sem (maidStruct D A) where
  chanceCPD node cfg := (κ node.val cfg).toPMF
  utilityFn _ utilityNode _ := by
    have h := utilityNode.property
    simp [maidStruct] at h

/-- Evaluate local causal kernels by the order-independent MAID/Bayesian-
network product semantics, retaining finite support in the result type. -/
def eval (D : DecisionDAG n) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (κ : LocalKernel D A) :
    Math.FinPMF (∀ i, A i) :=
  Math.FinPMF.ofPMF
    (MAID.evalAssignDist (maidStruct D A) (sem D A κ)
      (MAID.defaultPolicy (maidStruct D A)))

/-- The underlying PMF of `eval` is literally the existing MAID joint law. -/
@[simp] theorem eval_toPMF (D : DecisionDAG n) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (κ : LocalKernel D A) :
    (eval D A κ).toPMF =
      MAID.evalAssignDist (maidStruct D A) (sem D A κ)
        (MAID.defaultPolicy (maidStruct D A)) :=
  rfl

/-- Embed deterministic contingent plans as point-valued local kernels. -/
def deterministic (D : DecisionDAG n) {A : Fin n → Type}
    (σ : Strategy D A) : LocalKernel D A :=
  fun i history => Math.FinPMF.pure (σ i history)

/-- At the deterministic embedding's realized assignment, every MAID local
distribution is the expected point mass. -/
theorem nodeDist_deterministic (D : DecisionDAG n) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (σ : Strategy D A) (i : Fin n) :
    MAID.nodeDist (maidStruct D A) (sem D A (deterministic D σ))
        (MAID.defaultPolicy (maidStruct D A)) i (realize D σ) =
      PMF.pure (realize D σ i) := by
  unfold MAID.nodeDist
  simp only [maidStruct]
  change PMF.pure
      (σ i (fun parent => realize D σ parent.val)) =
    PMF.pure (realize D σ i)
  rw [realize_eq]

/-- Deterministic sparse-DAG realization is exactly the deterministic corner
of the Bayesian-network joint-law semantics. -/
@[simp] theorem eval_deterministic (D : DecisionDAG n) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (σ : Strategy D A) :
    eval D A (deterministic D σ) = Math.FinPMF.pure (realize D σ) := by
  apply Math.FinPMF.ext
  rw [eval_toPMF, Math.FinPMF.toPMF_pure]
  exact MAID.evalAssignDist_eq_pure_of_nodeDist
    (sem D A (deterministic D σ))
    (MAID.defaultPolicy (maidStruct D A))
    (maidStruct_naturalOrder D A) (realize D σ)
    (nodeDist_deterministic D A σ)

/-- Expected payoff under a causal joint law. This is the conventional
ex-ante interface for fixed chance kernels and behavioral node policies. -/
def expectedPayoff (D : DecisionDAG n) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (κ : LocalKernel D A)
    (utility : (∀ i, A i) → ι → ℝ) (player : ι) : ℝ :=
  Math.FinPMF.expect (eval D A κ) (fun path => utility path player)

/-- Expected payoff at a deterministic kernel profile reduces to the existing
deterministic continuation value. -/
@[simp] theorem expectedPayoff_deterministic (D : DecisionDAG n)
    (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (σ : Strategy D A)
    (utility : (∀ i, A i) → ι → ℝ) (player : ι) :
    expectedPayoff D A (deterministic D σ) utility player =
      utility (realize D σ) player := by
  simp [expectedPayoff]

/-! ## Fixed chance mechanisms and behavioral decision policies -/

variable {Player : Type} [DecidableEq Player]

/-- A player supplies a total profile of local behavioral kernels. Only nodes
designated as owned by that player are read. -/
abbrev PlayerPolicy (D : DecisionDAG n) (A : Fin n → Type) (_ : Player) :=
  LocalKernel D A

/-- Assemble fixed chance kernels and player-supplied behavioral kernels into
one causal law. `owner i = none` marks a chance node; `some p` marks a decision
node controlled by `p`. -/
def assemble (D : DecisionDAG n) {A : Fin n → Type}
    (owner : Fin n → Option Player) (chance : LocalKernel D A)
    (policy : ∀ player : Player,
      PlayerPolicy (Player := Player) D A player) : LocalKernel D A :=
  fun i => match owner i with
    | none => chance i
    | some player => policy player i

/-- Regroup a complete behavioral kernel profile as the redundant policy
supplied by every player. -/
def groupPolicy (D : DecisionDAG n) {A : Fin n → Type}
    (κ : LocalKernel D A) : ∀ player : Player,
      PlayerPolicy (Player := Player) D A player :=
  fun _ => κ

omit [DecidableEq Player] in
/-- If a complete kernel profile agrees with the fixed mechanisms at every
chance node, assembling its regrouping recovers it exactly. -/
theorem assemble_groupPolicy (D : DecisionDAG n) {A : Fin n → Type}
    (owner : Fin n → Option Player) (chance κ : LocalKernel D A)
    (hchance : ∀ i, owner i = none → κ i = chance i) :
    assemble D owner chance (groupPolicy D κ) = κ := by
  funext i history
  cases howner : owner i with
  | none =>
      simp only [assemble, howner]
      exact congrFun (hchance i howner).symm history
  | some player => simp [assemble, groupPolicy, howner]

/-- The strategic-form game of behavioral policies in a causal DAG with fixed
chance mechanisms. Payoffs are evaluated ex ante under the induced joint law.

This is a standard MAID behavioral-policy game. It does not identify
behavioral policies with mixed distributions over complete contingent plans;
that requires perfect recall. -/
def behavioralNFG (D : DecisionDAG n) (owner : Fin n → Option Player)
    (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (chance : LocalKernel D A)
    (utility : (∀ i, A i) → Player → ℝ) :
    NFG.NFGGame Player (PlayerPolicy (Player := Player) D A) where
  Outcome := Math.FinPMF (∀ i, A i)
  outcome policy := eval D A (assemble D owner chance policy)
  utility law player :=
    Math.FinPMF.expect law (fun path => utility path player)

/-- Compile the behavioral causal-DAG game through the common NFG kernel
bridge. -/
noncomputable def compileBehavioral (D : DecisionDAG n)
    (owner : Fin n → Option Player) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (chance : LocalKernel D A)
    (utility : (∀ i, A i) → Player → ℝ) : GameTheory.KernelGame Player :=
  (behavioralNFG D owner A chance utility).toKernelGame

/-- Behavioral player-form Nash for a causal DAG with fixed chance nodes. -/
def IsBehavioralNash (D : DecisionDAG n) (owner : Fin n → Option Player)
    (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (chance : LocalKernel D A)
    (utility : (∀ i, A i) → Player → ℝ)
    (policy : ∀ player : Player,
      PlayerPolicy (Player := Player) D A player) : Prop :=
  NFG.IsNashPure (behavioralNFG D owner A chance utility) policy

/-- The behavioral MAID-style policy game has exact kernel-game semantics. -/
theorem isBehavioralNash_iff_kernelNash (D : DecisionDAG n)
    (owner : Fin n → Option Player) (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Inhabited (A i)] (chance : LocalKernel D A)
    (utility : (∀ i, A i) → Player → ℝ)
    (policy : ∀ player : Player,
      PlayerPolicy (Player := Player) D A player) :
    IsBehavioralNash D owner A chance utility policy ↔
      (compileBehavioral D owner A chance utility).IsNash policy := by
  exact NFG.IsNashPure_iff_kernelGame
    (behavioralNFG D owner A chance utility) policy

end OpenGames.ShapeDAG.Causal
