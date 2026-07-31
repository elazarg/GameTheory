/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticBellmanExistence
import GameTheory.Concepts.Stochastic.AnalyticBellmanHierarchy
import GameTheory.Concepts.Stochastic.AnalyticPrescribedEndpointTailRecurrentChildBridge

/-!
# The attainable-endpoint correspondence, restarted branch

**Provenance.**  Question 64 (*target-coherent analytic child germs*) states
the endpoint correspondence

`𝒜_re(h', C) = { y : (0, y) ∈ closure Y_C }`

together with the exact restarted-coherence theorem: a restarted child germ
with endpoint `w` at the child entry exists *iff* `w ∈ 𝒜_re(h', C)`.  Up to
now that correspondence appeared in this repository only as a *hypothesis*:
the `ChildObligations` bundle of
`GameTheory.Concepts.Stochastic.AnalyticPrescribedEndpointTailRecurrentChildBridge`
carries fields `whole_vector_target` and `rank_decreases` that restate the
conclusion of Question 64 as an assumption.

This file is the first pass at the missing *definitional* layer.  It defines
the restarted branch of the correspondence as an actual set of payoff
vectors, proves the easy facts about it, and exhibits the exact way a
`ChildObligations`-style consumer is fed from a membership statement.  It
proves no part of Question 64.

**What is in scope.**

* `RestartedChildGerm G entry` — an analytic Bellman germ of the *same* game
  `G`, together with a designated entry state at which its endpoint is read.
* `attainableEndpoint G entry : Set (Payoff ι)` — the set of endpoint payoff
  vectors realized by restarted child germs at `entry`.
* `MemAttainableTarget` and the intro/elim lemmas.
* `AttainableTargetLabel` — two nodes carrying one common attainable target;
  its `whole_vector_target` lemma is exactly the field that
  `ChildObligations` assumes.
* `childObligationsOfAttainableTarget` — the de-smuggling constructor.

**What is explicitly out of scope.**

* The *inherited* branch of Question 64 (`w = T_C(0) V⁰`, equation (77))
  needs germ morphisms — Bellman/row/target morphisms whose cell, quotient,
  harmonic, jet, and account data commute.  This repository has no germ
  morphism, so the inherited branch is not defined here.
* The full `iff` of Theorem B (equation (78)) needs semialgebraic curve
  selection for a *child* continuation presentation `𝔠 = (Z_c, z'₀, s_c,
  A_c, q_c, g_c, U_c, Ξ_C)`.  This repository has no child continuation
  presentation: a `RestartedChildGerm` here is a germ of the ambient game
  read at a designated state, which is the weakest faithful reading of
  "restart".  The genuine restarted-child system, with its own public
  configuration space and legacy interface `Ξ_C`, is future work.
* Consequently `attainableEndpoint` is the *unconstrained* restarted
  correspondence: it carries no face, forbidden-row, quotient, account, or
  rank constraint.  It is therefore an over-approximation of Question 64's
  `𝒜_re(h', C)`, which is the honest direction for a *nonemptiness*
  statement but not for an exact characterization.

This file replaces nothing.  Nothing in
`AnalyticPrescribedEndpointTailRecurrentChildBridge` is modified; the
constructor below is built alongside it.
-/

set_option autoImplicit false

noncomputable section

open Math Math.OnlineLearning Math.Probability Set

namespace GameTheory
namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι)
  [Fintype G.State] [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-! ## Restarted child germs -/

/--
A **restarted child germ** of `G` at the designated entry state `entry`.

An `AnalyticBellmanGerm` solves the polynomial Bellman system of `G` at
*every* state simultaneously, and `AnalyticBellmanGerm.endpointValue` is a
function `G.State → Payoff ι`.  A germ therefore carries no intrinsic
starting state; the only thing a "restart at `entry`" adds is the
designation of the coordinate at which its endpoint vector is read.  This is
the lightest faithful bundling the repository supports, and it is
deliberately weaker than Question 64's restarted child: a genuine restarted
child would be a germ of a *child continuation presentation* with its own
public configuration space and legacy interface, which does not exist here.
-/
structure RestartedChildGerm (entry : G.State) where
  /-- The underlying analytic Bellman germ of the ambient game `G`. -/
  germ : G.AnalyticBellmanGerm

namespace RestartedChildGerm

variable {G}

/-- Every analytic Bellman germ of `G` restarts at every state of `G`. -/
def ofGerm (germ : G.AnalyticBellmanGerm) (entry : G.State) :
    G.RestartedChildGerm entry :=
  ⟨germ⟩

@[simp]
theorem germ_ofGerm (germ : G.AnalyticBellmanGerm) (entry : G.State) :
    (RestartedChildGerm.ofGerm germ entry).germ = germ :=
  rfl

/-- The endpoint payoff vector delivered by a restarted child germ at its
designated entry state.  This is the `w` of Question 64's equation (33). -/
def endpointTarget {entry : G.State} (child : G.RestartedChildGerm entry) :
    Payoff ι :=
  child.germ.endpointValue entry

@[simp]
theorem endpointTarget_ofGerm (germ : G.AnalyticBellmanGerm)
    (entry : G.State) :
    (RestartedChildGerm.ofGerm germ entry).endpointTarget =
      germ.endpointValue entry :=
  rfl

end RestartedChildGerm

/-! ## The attainable-endpoint correspondence -/

/--
The **attainable-endpoint correspondence** at `entry`: the set of payoff
vectors arising as the endpoint value of some restarted child germ.

This is the restarted branch of Question 64's correspondence
`𝒜_re(h', C)`, taken without the target constraints of the child Bellman
system (see the module docstring): no face selection, forbidden-row
condition, owner-history quotient, account status, or rank constraint is
imposed.  The inherited branch of the correspondence — targets that are
restrictions or affine images of the parent endpoint `V⁰` under a germ
morphism — is *not* defined here and is future work.
-/
def attainableEndpoint (entry : G.State) : Set (Payoff ι) :=
  {w | ∃ child : G.RestartedChildGerm entry, child.endpointTarget = w}

/-- Membership in the correspondence unfolded to the existence of an
analytic Bellman germ with the prescribed endpoint value at `entry`. -/
theorem mem_attainableEndpoint_iff {entry : G.State} {w : Payoff ι} :
    w ∈ G.attainableEndpoint entry ↔
      ∃ germ : G.AnalyticBellmanGerm, germ.endpointValue entry = w := by
  constructor
  · rintro ⟨child, rfl⟩
    exact ⟨child.germ, rfl⟩
  · rintro ⟨germ, rfl⟩
    exact ⟨RestartedChildGerm.ofGerm germ entry, rfl⟩

/-- Introduction from a restarted child germ. -/
theorem endpointTarget_mem_attainableEndpoint {entry : G.State}
    (child : G.RestartedChildGerm entry) :
    child.endpointTarget ∈ G.attainableEndpoint entry :=
  ⟨child, rfl⟩

/-- Introduction from a bare analytic Bellman germ. -/
theorem endpointValue_mem_attainableEndpoint
    (germ : G.AnalyticBellmanGerm) (entry : G.State) :
    germ.endpointValue entry ∈ G.attainableEndpoint entry :=
  G.mem_attainableEndpoint_iff.mpr ⟨germ, rfl⟩

/-- Elimination: membership yields an actual restarted child germ. -/
theorem exists_restartedChildGerm_of_mem_attainableEndpoint
    {entry : G.State} {w : Payoff ι} (hw : w ∈ G.attainableEndpoint entry) :
    ∃ child : G.RestartedChildGerm entry, child.endpointTarget = w :=
  hw

/-- Elimination: membership yields an actual analytic Bellman germ whose
endpoint value at `entry` is the prescribed vector. -/
theorem exists_analyticBellmanGerm_of_mem_attainableEndpoint
    {entry : G.State} {w : Payoff ι} (hw : w ∈ G.attainableEndpoint entry) :
    ∃ germ : G.AnalyticBellmanGerm, germ.endpointValue entry = w :=
  G.mem_attainableEndpoint_iff.mp hw

/-- **Vacuity probe.**  The correspondence is nonempty at every state of
every finite stochastic game with nonempty finite action sets.  This is
exactly the content of the proved `analyticBellmanGermExistence`: existence
of *some* child germ proves only that the correspondence is nonempty. -/
theorem attainableEndpoint_nonempty [∀ i, Nonempty (G.Act i)]
    (entry : G.State) :
    (G.attainableEndpoint entry).Nonempty := by
  obtain ⟨germ⟩ := analyticBellmanGermExistence.forGame G
  exact ⟨germ.endpointValue entry, G.endpointValue_mem_attainableEndpoint germ entry⟩

/-- The same fact packaged as a `Nonempty` instance-style statement. -/
theorem nonempty_restartedChildGerm [∀ i, Nonempty (G.Act i)]
    (entry : G.State) :
    Nonempty (G.RestartedChildGerm entry) := by
  obtain ⟨germ⟩ := analyticBellmanGermExistence.forGame G
  exact ⟨RestartedChildGerm.ofGerm germ entry⟩

/-! ### The correspondence is cut out by the undiscounted Bellman system

No *uniform numeric* bound on attainable endpoints is available from the
current library: the only germ-value bound in the repository,
`AnalyticBellmanGerm.finkBoundAt`, is defined from the germ's own value
coordinates and is therefore not a bound in terms of the game data.  What
*is* cheap is the structural constraint: every attainable endpoint is the
`entry` coordinate of a solution of the undiscounted (discount factor `1`)
stationary Bellman system of `G`, equivalently of a polynomial Bellman
solution whose discount-complement coordinate vanishes.  This is the
Lean-level shadow of Question 64's "constrained endpoint correspondence"; it
does *not* establish that the constraint is proper for any particular game.
-/

/-- Every attainable endpoint extends to a full solution of the
undiscounted stationary Bellman system. -/
theorem attainableEndpoint_subset_undiscountedBellmanValue (entry : G.State) :
    G.attainableEndpoint entry ⊆
      {w : Payoff ι |
        ∃ (x : G.StationaryMixedProfile) (V : G.State → Payoff ι),
          G.IsDiscountedStationaryBellmanEq 1 x V ∧ V entry = w} := by
  rintro w ⟨child, rfl⟩
  exact ⟨child.germ.endpointProfile, child.germ.endpointValue,
    child.germ.isDiscountedStationaryBellmanEq_endpoint, rfl⟩

/-- Every attainable endpoint is read off a polynomial Bellman solution with
vanishing discount-complement coordinate. -/
theorem attainableEndpoint_subset_zeroDiscountSolutionValue (entry : G.State) :
    G.attainableEndpoint entry ⊆
      {w : Payoff ι |
        ∃ assign : BellmanVar G → ℝ,
          G.IsPolynomialBellmanSolution assign ∧
            assign BellmanVar.disc = 0 ∧
            G.bellmanDecodeValue assign entry = w} := by
  rintro w ⟨child, rfl⟩
  exact ⟨child.germ.endpoint,
    child.germ.endpoint_isPolynomialBellmanSolution,
    child.germ.endpoint_discountCoordinate_eq_zero, rfl⟩

/-! ## De-smuggling `ChildObligations` -/

/--
`MemAttainableTarget G entry target` is Question 64's membership statement
`w ∈ 𝒜_re` for the restarted branch, with `w = target` and the child entry
`h'` represented by the state `entry`.

Under the exact restarted-coherence theorem this is *equivalent* to the
existence of a restarted child germ with endpoint `target` at `entry`.  Here
it is *defined* to be that existence (via `attainableEndpoint`); the content
that Question 64 adds — that the same set is cut out by the closure of the
constrained child root-value graph `Y_C` — is not formalized.
-/
def MemAttainableTarget (entry : G.State) (target : Payoff ι) : Prop :=
  target ∈ G.attainableEndpoint entry

theorem memAttainableTarget_iff {entry : G.State} {target : Payoff ι} :
    G.MemAttainableTarget entry target ↔
      ∃ germ : G.AnalyticBellmanGerm, germ.endpointValue entry = target :=
  G.mem_attainableEndpoint_iff

theorem memAttainableTarget_endpointValue
    (germ : G.AnalyticBellmanGerm) (entry : G.State) :
    G.MemAttainableTarget entry (germ.endpointValue entry) :=
  G.endpointValue_mem_attainableEndpoint germ entry

/--
**The de-smuggling datum.**  Two nodes of a recursion carry one common
target vector, and that vector is attainable as a restarted child endpoint
at `entry`.

This is the honest replacement for the bare equation
`nodeTarget child = nodeTarget parent` assumed by `ChildObligations`: the
equation is recovered (see `whole_vector_target`), but only from the strictly
stronger data that both nodes are *labelled by the same attainable target*.
The `attainable` field is what carries the Question 64 content; the two
labelling equations are the bookkeeping that the ambient recursion must
supply.
-/
structure AttainableTargetLabel (entry : G.State) {Node : Type*}
    (nodeTarget : Node → ι → ℝ) (parent child : Node) where
  /-- The common target vector carried by both nodes. -/
  target : Payoff ι
  /-- The target is a restarted child endpoint at `entry`. -/
  attainable : G.MemAttainableTarget entry target
  /-- The parent node is labelled by the target. -/
  parent_target : nodeTarget parent = target
  /-- The child node is labelled by the target. -/
  child_target : nodeTarget child = target

namespace AttainableTargetLabel

variable {G}

/-- The whole-vector target equation assumed by `ChildObligations`, derived
from a common attainable label. -/
theorem whole_vector_target {entry : G.State} {Node : Type*}
    {nodeTarget : Node → ι → ℝ} {parent child : Node}
    (label : G.AttainableTargetLabel entry nodeTarget parent child) :
    nodeTarget child = nodeTarget parent := by
  rw [label.child_target, label.parent_target]

/-- A labelled pair is never vacuous: it produces an actual analytic Bellman
germ whose endpoint value at `entry` is the child's target vector. -/
theorem exists_analyticBellmanGerm {entry : G.State} {Node : Type*}
    {nodeTarget : Node → ι → ℝ} {parent child : Node}
    (label : G.AttainableTargetLabel entry nodeTarget parent child) :
    ∃ germ : G.AnalyticBellmanGerm,
      germ.endpointValue entry = nodeTarget child := by
  obtain ⟨germ, hgerm⟩ := G.memAttainableTarget_iff.mp label.attainable
  exact ⟨germ, by rw [hgerm, label.child_target]⟩

/-- The canonical label attached to a germ: both nodes are labelled by that
germ's endpoint value at `entry`. -/
def ofGerm {entry : G.State} {Node : Type*} {nodeTarget : Node → ι → ℝ}
    {parent child : Node} (germ : G.AnalyticBellmanGerm)
    (hparent : nodeTarget parent = germ.endpointValue entry)
    (hchild : nodeTarget child = germ.endpointValue entry) :
    G.AttainableTargetLabel entry nodeTarget parent child where
  target := germ.endpointValue entry
  attainable := G.memAttainableTarget_endpointValue germ entry
  parent_target := hparent
  child_target := hchild

end AttainableTargetLabel

namespace AnalyticBellmanGerm
namespace TailReachableRecurrentClassCandidate

variable {G} [DecidableEq G.State]
variable {germ : G.AnalyticBellmanGerm}
  {who : ι} {entry : G.State}
  {startEpoch : ℕ}
  {valid :
    ∀ epoch : ℕ,
      shiftedUniversalEpochScale startEpoch epoch ∈
        Ioo (0 : ℝ) germ.radius}
  {evidence :
    TailReachableEndpointTransportCirculationEvidence
      germ who entry startEpoch valid}

/--
**The de-smuggling step.**  A `ChildObligations` bundle assembled from a
membership statement in the attainable-endpoint correspondence together with
the residual obligations.

Compared with the bare structure in
`AnalyticPrescribedEndpointTailRecurrentChildBridge`, the field
`whole_vector_target` is no longer assumed: it is *derived* from
`label.whole_vector_target`, whose content is that both nodes carry one
common target lying in `attainableEndpoint` at the child's ambient entry
state `(nodeEntry child).1`.

The residual fields are still assumed, and this is the point of the
construction — they are exactly what the correspondence does *not* supply:

* `parent_entry`, `child_entry` — the graph-theoretic identification of both
  node entries with the positive-charge class representative;
* `rank_decreases` — the strict rank descent, which is
  `Question 64` rank-faithfulness and is *not* implied by endpoint equality
  (see the final section of the Question 64 answer: "endpoint equality alone
  proves none of the rank, row, quotient, face, or account assertions");
* `legal_entry_interface` — the application-specific legal-entry evidence.

Note also that the `label` hypothesis is strictly stronger than membership
alone: membership of a single vector cannot produce an equality of two node
labels, so the two labelling equations must accompany it.
-/
def childObligationsOfAttainableTarget
    (candidate : TailReachableRecurrentClassCandidate evidence)
    {Rank Node : Type*}
    (nodeEntry : Node → TailTransportActiveState evidence)
    (nodeTarget : Node → ι → ℝ)
    (nodeRank : Node → Rank)
    (rankLt : Rank → Rank → Prop)
    (LegalEntryInterface : Node → Prop)
    (parent child : Node)
    (label :
      G.AttainableTargetLabel (nodeEntry child).1 nodeTarget parent child)
    (parent_entry :
      nodeEntry parent =
        evidence.chargedClass.positiveClass.representative)
    (child_entry :
      nodeEntry child =
        evidence.chargedClass.positiveClass.representative)
    (rank_decreases : rankLt (nodeRank child) (nodeRank parent))
    (legal_entry_interface : LegalEntryInterface parent) :
    candidate.ChildObligations
      nodeEntry nodeTarget nodeRank rankLt LegalEntryInterface parent where
  child := child
  parent_entry := parent_entry
  child_entry := child_entry
  whole_vector_target := label.whole_vector_target
  rank_decreases := rank_decreases
  legal_entry_interface := legal_entry_interface

/-- The composed consumer: the recurrent-class candidate becomes a public
recurrent child once the whole-vector target is supplied by the
attainable-endpoint correspondence and the residual entry, rank, and
legal-interface obligations are supplied separately. -/
def toPublicRecurrentClassChildOfAttainableTarget
    (candidate : TailReachableRecurrentClassCandidate evidence)
    {Rank Node : Type*}
    (nodeEntry : Node → TailTransportActiveState evidence)
    (nodeTarget : Node → ι → ℝ)
    (nodeRank : Node → Rank)
    (rankLt : Rank → Rank → Prop)
    (LegalEntryInterface : Node → Prop)
    (parent child : Node)
    (label :
      G.AttainableTargetLabel (nodeEntry child).1 nodeTarget parent child)
    (parent_entry :
      nodeEntry parent =
        evidence.chargedClass.positiveClass.representative)
    (child_entry :
      nodeEntry child =
        evidence.chargedClass.positiveClass.representative)
    (rank_decreases : rankLt (nodeRank child) (nodeRank parent))
    (legal_entry_interface : LegalEntryInterface parent) :
    PublicRecurrentClassChild
      (tailTransportActiveKernel evidence)
      nodeEntry nodeTarget nodeRank rankLt
      LegalEntryInterface parent :=
  candidate.toPublicRecurrentClassChild
    nodeEntry nodeTarget nodeRank rankLt LegalEntryInterface parent
    (candidate.childObligationsOfAttainableTarget
      nodeEntry nodeTarget nodeRank rankLt LegalEntryInterface
      parent child label parent_entry child_entry rank_decreases
      legal_entry_interface)

/-- The germ extracted from the label of a de-smuggled child: the child's
target vector really is realized by an analytic Bellman germ at the child's
ambient entry state.  This is what distinguishes the construction above from
the bare assumption it replaces. -/
theorem exists_analyticBellmanGerm_of_label
    {Node : Type*}
    {nodeEntry : Node → TailTransportActiveState evidence}
    {nodeTarget : Node → ι → ℝ}
    {parent child : Node}
    (label :
      G.AttainableTargetLabel (nodeEntry child).1 nodeTarget parent child) :
    ∃ g : G.AnalyticBellmanGerm,
      g.endpointValue (nodeEntry child).1 = nodeTarget child :=
  label.exists_analyticBellmanGerm

end TailReachableRecurrentClassCandidate
end AnalyticBellmanGerm

end StochasticGame
end GameTheory
