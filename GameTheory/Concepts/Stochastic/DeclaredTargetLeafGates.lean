/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.AnalyticEndpointLeafSelection
import GameTheory.Concepts.Stochastic.PureExternalityCycleHolonomy
import Math.LinearAlgebra.OrientedAccountBridge
import Math.LinearAlgebra.OwnerTypedDualLifting

/-!
# Declared-target nodes and the leaf-facing gate data

The analytic endpoint atlas classifies a germ into an
`AnalyticEndpointAtlasLeaf` whose nonsemantic branches all name a
`*ReconstructionAt` obligation *at the germ's own endpoint value*.  The three
finite interface cores

* `Math.LinearAlgebra.OwnerLabeledFlowHolonomy` (gluing / holonomy),
* `Math.LinearAlgebra.OwnerTypedDualLifting` (owner custody / typed lifting),
* `Math.LinearAlgebra.OrientedAccountBridge` (oriented exact account bridge),

are, by construction, *game-free* finite linear algebra.  Nothing in the
repository currently connects them to an actual analytic endpoint leaf.  This
file is that connection layer, built **additively**: it edits no existing file,
restructures no existing `*ReconstructionAt` record, and touches no umbrella.

## What a declared-target node is, and what it deliberately is not

`DeclaredTargetNode` is the neutral carrier: a germ, its processed
endpoint-harmonic span, a public entry state, and a **declared** target payoff
vector `w`.  It carries

* no identification of `w` with `germ.endpointValue entry`,
* no implementability claim for `w`,
* no adaptive certificate,
* no uniform-payoff assumption,
* no public-lottery assumption.

The identification `w = germ.endpointValue entry` is available as the *named
predicate* `DeclaredTargetNode.IsEndpointDeclared` and as the *constructor*
`DeclaredTargetNode.ofEndpoint`; it is a theorem in special cases and never a
field.  `PureExternalityCycleGates.exists_not_isEndpointDeclared` exhibits a
concrete node of the pure-externality cycle at which it **fails**, so the
absence of the coercion is machine-checked and not merely a naming
convention.

## The extraction, honestly

The germ API (`AnalyticBellmanGerm`, `EndpointHarmonicJetSpan`,
`endpointValue`, `endpointFinkPoint`) does **not by itself** package a tagged
owner-labeled row system in the leaf-gate format, and it does not produce
"genuine unilateral Bellman rows of player `i` in a legal public response
context".  This foundational file therefore keeps `NodeFlowRows` neutral.
The downstream module `AnalyticEndpointBellmanRowCompiler` canonically
packages **all actual endpoint owned pure deviations** from the raw analytic
obstruction data.  It deliberately does not add the missing legal-public-
response interpretation.

Therefore `NodeFlowRows` takes the row system as a **component** and ties it to
the node by the coherence that is checkable today:

1. *Vertex coherence.*  Vertices are literally `G.State`; the row source map
   is `src : Row → G.State`.
2. *Owner coherence.*  Row labels are literally the player type `ι`.
3. *Stochasticity.*  `IsStochastic transition` is a field.
4. *Entry coherence.*  `entry_isSource` requires some row to be sourced at the
   node's entry state.  It is a real constraint: an empty row system fails it.
5. *Target-relative charge, definitionally.*  The record carries a gross row
   gain, and `NodeFlowRows.charge` is **defined** as
   `grossGain r - node.target (ownerOf r)`.  The charge therefore cannot drift
   away from the declared target; changing `w` changes every gate verdict
   through this one definition.
6. *Endpoint-kernel coherence, as a refutable predicate.*
   `NodeFlowRows.IsEndpointKernelTagged` says that the row transition weights
   reproduce the germ's endpoint **pure-deviation state kernels**
   `G.finkPureDeviationStateKernel germ.endpointFinkPoint` in exactly the
   pairing form `∑ v, P r v * H v` that `IsAccountPotential` consumes.  This
   one is genuinely germ-derived; it is a `Prop`, not a field, so it stays
   assumable *and* refutable (`selfLoopRows_not_isEndpointKernelTagged`).

What is **not required by this neutral record** is that `grossGain r` came
from a genuine unilateral deviation row.  The manual
`PureExternalityCycleHolonomy.rowCharge` instantiation still reads it off the
payoff table by hand.  `AnalyticEndpointBellmanRowCompiler` closes precisely
that actual-data gap for the canonical all-state/all-owner/all-action endpoint
row family, while leaving public-response legality and recursive-child
realization as separate obligations.

For the custody core the analogous coherence is sharper: `NodeCustodyGate`
fixes the boundary-target index type of the `TypedCell` to be `ι` itself, so
the cell's target coordinates *are* the payoff coordinates of the declared
target, and the field `target_memFull` checks that the declared target is a
feasible point of the full typed system.  That single field is exactly the
feasibility hypothesis `hasTypedLift_iff_validOnVisible_of_full` needs, so the
Farkas adapter at a node is unconditional.

## Gate records and adapters

Three additive records, each carrying its node and its finite-core system:

* `NodeGluingGate` — flow rows; verdict `Glues := ZeroHolonomy`.  Adapter
  `glues_iff_hasAccountPotential` is one application of
  `zeroHolonomy_iff_exists_accountPotential`.
* `NodeAccountBridgeGate` — a gluing gate refined by a strictly positive
  circulation witness; verdict `Bridges := ∃ H, IsExactBridge`.  Adapter
  `bridges_iff_neutralGlues` is unconditional *on this record*, because the
  witness discharges `HasFullSupportCirculation`.  The record can fail to
  exist — that is the `ParallelRows` separation, preserved as
  `noWitness_of_circulation_eq_zero`.
* `NodeCustodyGate` — a typed cell whose target coordinates are the declared
  target's; verdict `Lifts i α β := HasTypedLift`.  Adapter
  `lifts_iff_validVisible` is one application of
  `hasTypedLift_iff_validOnVisible_of_full`.

Each gate exposes a two-valued `GateVerdict` and a `pass ∨ fail` dichotomy, so
a future dispatcher can case on the verdict.  Gate failure is always
accompanied by a *witness type* (`FarkasWitness`, `VisibleEscape`), so the
falsifier zoo of the three cores survives the transport to nodes.

## Vacuity probes

Every new `Prop` and structure is probed.

* `DeclaredTargetNode` is inhabited for every germ and every `w`
  (`declare`); that is the point of neutrality.  `IsEndpointDeclared` is not
  automatic (`exists_not_isEndpointDeclared`).
* `NodeFlowRows` is inhabited at every node by `selfLoopRows`, and the
  resulting gluing gate **passes** when the declared target coordinate is
  nonnegative and **fails** when it is negative — so neither verdict is
  vacuous.
* `IsEndpointKernelTagged` is refuted by `selfLoopRows` on the
  pure-externality cycle, and satisfied by `cycleRows` there.
* `NodeCustodyGate` is inhabited by `trivialCustodyGate`, whose typed cell has
  no rows at all; it lifts `0` at bound `0` and lifts **no** nonzero
  functional at any bound.

## Instantiation

`PureExternalityCycleGates` builds the records on the two explicit germs of
`PureExternalityCycleGerm`, with the tagged rows of
`PureExternalityCycleHolonomy`.  Both nodes are endpoint-declared, and the
gates separate:

* at `prescribedGerm` with declared target `(0, 0)` the gluing gate **fails**,
  no account potential exists, and no exact bridge exists — even though the
  full-support witness is present;
* at `oneGerm` with declared target `(1, 1)` the charge is identically `0`,
  the gluing gate **passes**, and an exact bridge exists.

So the gate verdict is not a function of `IsEndpointDeclared`: both nodes
declare their germ's endpoint value, and they land on opposite sides.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability
open Math.LinearAlgebra.OwnerLabeledFlowHolonomy
open Math.LinearAlgebra.OrientedAccountBridge
open Math.LinearAlgebra.OwnerTypedDualLifting

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-! ## The neutral declared-target node -/

variable (G) in
/-- A **declared-target node**: a germ, the processed endpoint-harmonic span
carried alongside it, a public entry state, and a declared target payoff
vector.

The node is deliberately neutral.  It has no field identifying `target` with
`germ.endpointValue entry`, no implementability claim, no adaptive
certificate, no uniform-payoff assumption and no public-lottery assumption.
Everything of that kind is a separate predicate or a separate record. -/
structure DeclaredTargetNode where
  /-- The analytic Bellman germ the node sits on. -/
  germ : G.AnalyticBellmanGerm
  /-- The processed endpoint-harmonic jet span carried at the node. -/
  span : germ.EndpointHarmonicJetSpan
  /-- The public entry state. -/
  entry : G.State
  /-- The **declared** target payoff vector.  A free parameter: nothing in
  this structure ties it to the germ. -/
  target : Payoff ι

namespace DeclaredTargetNode

/-- The germ's endpoint value function, as an accessor. -/
def endpointValue (node : DeclaredTargetNode G) : G.State → Payoff ι :=
  node.germ.endpointValue

/-- The germ's endpoint value at the node's own entry state. -/
def endpointAtEntry (node : DeclaredTargetNode G) : Payoff ι :=
  node.germ.endpointValue node.entry

/-- The declared discrepancy: declared target minus the germ's endpoint value
at the entry.  This is the vector the gates below charge against. -/
def targetGap (node : DeclaredTargetNode G) : Payoff ι :=
  fun i => node.target i - node.endpointAtEntry i

/-- The node's target coordinate owned by a player. -/
def targetAt (node : DeclaredTargetNode G) (i : ι) : ℝ := node.target i

/-- **The identification, as a predicate and never as a field.**  The declared
target coincides with the germ's endpoint value at the entry.

There is intentionally no coercion `DeclaredTargetNode → (target = endpoint)`
and no default instance producing one.  `ofEndpoint` is the constructor that
declares the endpoint; `PureExternalityCycleGates.exists_not_isEndpointDeclared`
shows that other nodes exist. -/
def IsEndpointDeclared (node : DeclaredTargetNode G) : Prop :=
  node.target = node.endpointAtEntry

theorem isEndpointDeclared_iff_targetGap_eq_zero (node : DeclaredTargetNode G) :
    node.IsEndpointDeclared ↔ node.targetGap = 0 := by
  constructor
  · intro h
    have h' : node.target = node.endpointAtEntry := h
    funext i
    simp only [targetGap, h', Pi.zero_apply, sub_self]
  · intro h
    funext i
    have hi := congrFun h i
    simp only [targetGap, Pi.zero_apply] at hi
    linarith

/-- Declare an arbitrary target at a germ, span and entry.  Totality of this
constructor in its last argument *is* the neutrality of the node type. -/
def declare (germ : G.AnalyticBellmanGerm) (span : germ.EndpointHarmonicJetSpan)
    (entry : G.State) (w : Payoff ι) : DeclaredTargetNode G where
  germ := germ
  span := span
  entry := entry
  target := w

@[simp] theorem declare_target (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) (w : Payoff ι) :
    (declare germ span entry w).target = w := rfl

@[simp] theorem declare_entry (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) (w : Payoff ι) :
    (declare germ span entry w).entry = entry := rfl

@[simp] theorem declare_germ (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) (w : Payoff ι) :
    (declare germ span entry w).germ = germ := rfl

/-- The endpoint-declared node: the one special case in which the declared
target *is* the germ's endpoint value.  Provided as a constructor precisely so
that the general node type does not have to assume it. -/
def ofEndpoint (germ : G.AnalyticBellmanGerm) (span : germ.EndpointHarmonicJetSpan)
    (entry : G.State) : DeclaredTargetNode G :=
  declare germ span entry (germ.endpointValue entry)

theorem isEndpointDeclared_ofEndpoint (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) :
    (ofEndpoint germ span entry).IsEndpointDeclared := rfl

/-- **Vacuity probe for the node type.**  The zero target is always
declarable, on every germ, span and entry: the node type constrains nothing.
Whether that zero declaration happens to be the endpoint declaration is a
separate, generally false, question. -/
theorem isEndpointDeclared_declare_zero_iff (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan) (entry : G.State) :
    (declare germ span entry 0).IsEndpointDeclared ↔
      germ.endpointValue entry = 0 := by
  constructor
  · intro h
    exact ((show (0 : Payoff ι) = germ.endpointValue entry from h)).symm
  · intro h
    exact congrArg (fun v => v) h.symm

end DeclaredTargetNode

/-! ## Owner-labeled flow rows at a declared-target node -/

/-- The owner-labeled flow row system supplied at a declared-target node.

Vertices are the game's states and owners are the game's players, so those two
coherences are typing.  This generic interface permits `src`, `transition`,
`ownerOf` and `grossGain` to be supplied; the downstream canonical endpoint
compiler instead derives all four.  Two coherence fields are carried here;
a third, `IsEndpointKernelTagged`, is a separate refutable predicate for
arbitrary supplied systems. -/
structure NodeFlowRows (node : DeclaredTargetNode G) (Row : Type) where
  /-- The source state of each row. -/
  src : Row → G.State
  /-- The row-stochastic transition weights of each row. -/
  transition : Row → G.State → ℝ
  /-- The owning player of each row. -/
  ownerOf : Row → ι
  /-- The gross (target-independent) gain carried by each row.  The generic
  interface accepts it as data; `AnalyticEndpointBellmanRowCompiler` derives
  it for canonical actual endpoint pure-deviation rows. -/
  grossGain : Row → ℝ
  /-- **Coherence.**  The transition weights really are a stochastic matrix. -/
  stochastic : IsStochastic transition
  /-- **Coherence.**  Some row is sourced at the node's entry state.  An empty
  row system fails this, so it is not vacuous. -/
  entry_isSource : ∃ r : Row, src r = node.entry

namespace NodeFlowRows

variable {node : DeclaredTargetNode G} {Row : Type}

/-- **The target-relative row charge, by definition.**  The declared target
enters the finite core through this single definition: the charge of a row is
its gross gain minus the declared target coordinate of the row's owner.

Within the neutral row record this is the coherence between the node's
declared target and the finite flow system, and it is definitional rather than
assumed.  Canonically compiled rows additionally identify `grossGain` with
the semantic endpoint pure-deviation stage payoff. -/
def charge (S : NodeFlowRows node Row) : Row → ℝ :=
  fun r => S.grossGain r - node.target (S.ownerOf r)

theorem charge_apply (S : NodeFlowRows node Row) (r : Row) :
    S.charge r = S.grossGain r - node.target (S.ownerOf r) := rfl

/-- When the declared target vanishes the charge is the gross gain. -/
theorem charge_eq_grossGain (S : NodeFlowRows node Row)
    (h : node.target = 0) : S.charge = S.grossGain := by
  funext r
  simp [charge, h]

/-- **Germ coherence, as a refutable predicate.**  The row transition weights
reproduce the germ's endpoint pure-deviation state kernels, in exactly the
pairing form `∑ v, P r v * H v` consumed by
`OwnerLabeledFlowHolonomy.IsAccountPotential`.

`act` supplies the deviation action carried by each row.  This is the one
coherence that is genuinely derived from the germ rather than declared; it is
a `Prop` so that it can be assumed and refuted. -/
def IsEndpointKernelTagged (S : NodeFlowRows node Row)
    (act : ∀ r : Row, G.Act (S.ownerOf r)) : Prop :=
  ∀ (r : Row) (w : G.State → ℝ),
    expect (G.finkPureDeviationStateKernel node.germ.endpointFinkPoint
      (S.src r) (S.ownerOf r) (act r)) w = ∑ v, S.transition r v * w v

/-- The usable form of the germ coherence: the one-step drift term of the
finite core is the germ's endpoint pure-deviation continuation. -/
theorem sum_transition_mul_eq_expect {S : NodeFlowRows node Row}
    {act : ∀ r : Row, G.Act (S.ownerOf r)} (h : S.IsEndpointKernelTagged act)
    (r : Row) (H : G.State → ℝ) :
    (∑ v, S.transition r v * H v) =
      expect (G.finkPureDeviationStateKernel node.germ.endpointFinkPoint
        (S.src r) (S.ownerOf r) (act r)) H :=
  (h r H).symm

end NodeFlowRows

section StateDecidable

variable [DecidableEq G.State]

namespace NodeFlowRows

/-! ### The trivial row system, used as the vacuity probe -/

/-- The one-row self-loop at the node's entry, owned by a chosen player and
carrying zero gross gain.  This is the trivial witness the vacuity probes use:
its charge is `-target owner`. -/
def selfLoopRows (node : DeclaredTargetNode G) (owner : ι) :
    NodeFlowRows node Unit where
  src := fun _ => node.entry
  transition := fun _ v => if v = node.entry then 1 else 0
  ownerOf := fun _ => owner
  grossGain := fun _ => 0
  stochastic :=
    { nonneg := fun _ v => by positivity
      row_sum := fun _ => by simp }
  entry_isSource := ⟨(), rfl⟩

@[simp] theorem selfLoopRows_charge (node : DeclaredTargetNode G) (owner : ι)
    (r : Unit) : (selfLoopRows node owner).charge r = -node.target owner :=
  zero_sub _

/-- The unit occupation of the self-loop is a circulation. -/
theorem isCirculation_selfLoop_one (node : DeclaredTargetNode G) (owner : ι) :
    IsCirculation (selfLoopRows node owner).src
      (selfLoopRows node owner).transition (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun v => ?_⟩
  simp only [incidence, selfLoopRows, one_mul]
  by_cases h : v = node.entry
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- The holonomy of the self-loop occupation is minus the declared target
coordinate of the owner. -/
theorem holonomy_selfLoop_one (node : DeclaredTargetNode G) (owner : ι) :
    holonomy (selfLoopRows node owner).charge (fun _ => 1) =
      -node.target owner := by
  simp only [holonomy, selfLoopRows_charge]
  simp

end NodeFlowRows

/-! ## Gate verdicts -/

/-- The two-valued verdict a leaf-facing gate returns.  It exists so that a
future dispatcher can `cases` on a gate outcome without unfolding the
underlying `Prop`. -/
inductive GateVerdict : Type
  /-- The gate is passed. -/
  | pass
  /-- The gate is failed. -/
  | fail
  deriving DecidableEq, Repr

/-- The verdict attached to a decidable gate proposition. -/
def verdictOf (p : Prop) [Decidable p] : GateVerdict := if p then .pass else .fail

@[simp] theorem verdictOf_eq_pass_iff (p : Prop) [Decidable p] :
    verdictOf p = GateVerdict.pass ↔ p := by
  unfold verdictOf
  split <;> simp_all

@[simp] theorem verdictOf_eq_fail_iff (p : Prop) [Decidable p] :
    verdictOf p = GateVerdict.fail ↔ ¬ p := by
  unfold verdictOf
  split <;> simp_all

/-! ## Gate 1: the gluing (holonomy) gate -/

/-- **The gluing gate at a declared-target node.**  It carries the node and
the owner-labeled flow system built on the node's data.  Its verdict is the
gluing condition for the target-relative charge. -/
structure NodeGluingGate (G : StochasticGame ι)
    [Fintype G.State] [DecidableEq G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
    (Row : Type) where
  /-- The declared-target node the gate sits at. -/
  node : DeclaredTargetNode G
  /-- The owner-labeled flow rows supplied at that node. -/
  rows : NodeFlowRows node Row

namespace NodeGluingGate

variable {Row : Type}

/-- Build a gluing gate from a row system. -/
def of {node : DeclaredTargetNode G} (rows : NodeFlowRows node Row) :
    NodeGluingGate G Row where
  node := node
  rows := rows

@[simp] theorem of_node {node : DeclaredTargetNode G}
    (rows : NodeFlowRows node Row) : (of rows).node = node := rfl

@[simp] theorem of_src {node : DeclaredTargetNode G}
    (rows : NodeFlowRows node Row) (r : Row) :
    (of rows).rows.src r = rows.src r := rfl

@[simp] theorem of_transition {node : DeclaredTargetNode G}
    (rows : NodeFlowRows node Row) (r : Row) (v : G.State) :
    (of rows).rows.transition r v = rows.transition r v := rfl

@[simp] theorem of_charge {node : DeclaredTargetNode G}
    (rows : NodeFlowRows node Row) (r : Row) :
    (of rows).rows.charge r = rows.charge r := rfl

variable [Fintype Row]

/-- **The gate-pass proposition.**  Every circulation of the node's row system
pairs nonpositively with the target-relative charge. -/
def Glues (gate : NodeGluingGate G Row) : Prop :=
  ZeroHolonomy gate.rows.src gate.rows.transition gate.rows.charge

/-- The dual datum: a single scalar account potential over the game's states
discharging every target-relative row charge. -/
def HasAccountPotential (gate : NodeGluingGate G Row) : Prop :=
  ∃ H : G.State → ℝ,
    IsAccountPotential gate.rows.src gate.rows.transition gate.rows.charge H

/-- **Adapter, at a node.**  A one-line consumer of
`zeroHolonomy_iff_exists_accountPotential`. -/
theorem glues_iff_hasAccountPotential (gate : NodeGluingGate G Row) :
    gate.Glues ↔ gate.HasAccountPotential :=
  zeroHolonomy_iff_exists_accountPotential _ _ _

/-- The easy half, in the direction a dispatcher consumes. -/
theorem glues_of_hasAccountPotential {gate : NodeGluingGate G Row}
    (h : gate.HasAccountPotential) : gate.Glues :=
  (gate.glues_iff_hasAccountPotential).mpr h

/-- **The typed falsifier at a node.**  A circulation of the node's row system
whose pairing with the target-relative charge is strictly positive.  This is
the Farkas certificate the core theorem manufactures on gate failure. -/
structure FarkasWitness (gate : NodeGluingGate G Row) : Type where
  /-- The offending flow. -/
  flow : Row → ℝ
  /-- It is a circulation of the node's row system. -/
  isCirculation : IsCirculation gate.rows.src gate.rows.transition flow
  /-- It charges the declared target strictly positively. -/
  holonomy_pos : 0 < holonomy gate.rows.charge flow

/-- Gate failure is exactly the existence of the typed falsifier. -/
theorem nonempty_farkasWitness_iff_not_glues (gate : NodeGluingGate G Row) :
    Nonempty gate.FarkasWitness ↔ ¬ gate.Glues := by
  constructor
  · rintro ⟨w⟩ hglue
    have := hglue w.flow w.isCirculation
    linarith [w.holonomy_pos]
  · intro h
    by_contra hcon
    refine h fun η hη => ?_
    by_contra hle
    exact hcon ⟨⟨η, hη, not_le.mp hle⟩⟩

/-- **The dispatcher dichotomy.**  Either the gluing gate passes, or the
falsifier zoo supplies a typed witness.  The two cases are exclusive by
`nonempty_farkasWitness_iff_not_glues`. -/
theorem glues_or_nonempty_farkasWitness (gate : NodeGluingGate G Row) :
    gate.Glues ∨ Nonempty gate.FarkasWitness := by
  by_cases h : gate.Glues
  · exact Or.inl h
  · exact Or.inr ((gate.nonempty_farkasWitness_iff_not_glues).mpr h)

/-- The gate verdict, for a dispatcher that wants to `cases` on data. -/
def verdict (gate : NodeGluingGate G Row) : GateVerdict :=
  @verdictOf gate.Glues (Classical.propDecidable _)

@[simp] theorem verdict_eq_pass_iff (gate : NodeGluingGate G Row) :
    gate.verdict = GateVerdict.pass ↔ gate.Glues :=
  @verdictOf_eq_pass_iff gate.Glues (Classical.propDecidable _)

@[simp] theorem verdict_eq_fail_iff (gate : NodeGluingGate G Row) :
    gate.verdict = GateVerdict.fail ↔ ¬ gate.Glues :=
  @verdictOf_eq_fail_iff gate.Glues (Classical.propDecidable _)

/-! ### Vacuity probes for the gluing gate -/

/-- **Positive probe.**  A nonpositive target-relative charge always glues. -/
theorem glues_of_charge_nonpos {gate : NodeGluingGate G Row}
    (h : ∀ r, gate.rows.charge r ≤ 0) : gate.Glues :=
  zeroHolonomy_of_charge_nonpos h

/-- **Trivial-witness probe, pass side.**  The self-loop row system at a node
whose declared target coordinate for the owner is nonnegative passes the
gate. -/
theorem glues_selfLoop_of_target_nonneg (node : DeclaredTargetNode G) (owner : ι)
    (h : 0 ≤ node.target owner) :
    (of (NodeFlowRows.selfLoopRows node owner)).Glues :=
  zeroHolonomy_of_charge_nonpos fun r => by
    change (NodeFlowRows.selfLoopRows node owner).charge r ≤ 0
    rw [NodeFlowRows.selfLoopRows_charge]
    linarith

/-- **Trivial-witness probe, fail side.**  The same self-loop row system at a
node with a strictly negative declared target coordinate *fails* the gate.  So
the trivial witness does not satisfy the gate automatically: neither verdict is
vacuous. -/
theorem not_glues_selfLoop_of_target_neg (node : DeclaredTargetNode G) (owner : ι)
    (h : node.target owner < 0) :
    ¬ (of (NodeFlowRows.selfLoopRows node owner)).Glues := by
  intro hglue
  have hle : holonomy (NodeFlowRows.selfLoopRows node owner).charge (fun _ => 1) ≤ 0 :=
    hglue (fun _ => 1) (NodeFlowRows.isCirculation_selfLoop_one node owner)
  rw [NodeFlowRows.holonomy_selfLoop_one] at hle
  linarith

end NodeGluingGate

/-! ## Gate 2: the oriented account-bridge gate -/

/-- **The oriented account-bridge gate at a declared-target node.**

It refines the gluing gate by a strictly positive circulation witness — the
finite shadow of the reachability/recurrence side condition, witnessing that
the cone of circulations spans the whole signed cycle space.  Carrying the
witness as data — rather than assuming `HasFullSupportCirculation` globally —
is what makes the two-sided adapter below unconditional *on this record* while
leaving the hypothesis refutable in general: `ParallelRows` admits no such
witness, and `noWitness_of_circulation_eq_zero` records that. -/
structure NodeAccountBridgeGate (G : StochasticGame ι)
    [Fintype G.State] [DecidableEq G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
    (Row : Type) [Fintype Row] extends NodeGluingGate G Row where
  /-- A circulation charging every row strictly positively. -/
  witness : Row → ℝ
  /-- It really is a circulation of the node's row system. -/
  witness_isCirculation : IsCirculation rows.src rows.transition witness
  /-- It really is strictly positive on every row. -/
  witness_pos : ∀ r, 0 < witness r

namespace NodeAccountBridgeGate

variable {Row : Type} [Fintype Row]

/-- The record's witness discharges the full-support hypothesis. -/
theorem hasFullSupportCirculation (gate : NodeAccountBridgeGate G Row) :
    HasFullSupportCirculation gate.rows.src gate.rows.transition :=
  ⟨gate.witness, gate.witness_isCirculation, gate.witness_pos⟩

/-- **The gate-pass proposition.**  The target-relative charge is an exact
coboundary of a scalar potential on the game's states. -/
def Bridges (gate : NodeAccountBridgeGate G Row) : Prop :=
  ∃ H : G.State → ℝ,
    IsExactBridge gate.rows.src gate.rows.transition gate.rows.charge H

/-- The two-sided cycle criterion at the node. -/
def NeutralGlues (gate : NodeAccountBridgeGate G Row) : Prop :=
  NeutralHolonomy gate.rows.src gate.rows.transition gate.rows.charge

/-- One ledger per orientation at the node, with the two potentials allowed
to differ. -/
def HasBothOrientationsAt (gate : NodeAccountBridgeGate G Row) : Prop :=
  HasBothOrientations gate.rows.src gate.rows.transition gate.rows.charge

/-- **Adapter, unconditional.**  One ledger per orientation is exactly the
two-sided cycle criterion. -/
theorem hasBothOrientationsAt_iff_neutralGlues
    (gate : NodeAccountBridgeGate G Row) :
    gate.HasBothOrientationsAt ↔ gate.NeutralGlues :=
  hasBothOrientations_iff_neutralHolonomy _ _ _

/-- **Adapter, unconditional easy direction.**  An exact bridge makes every
circulation pair to exactly zero. -/
theorem neutralGlues_of_bridges {gate : NodeAccountBridgeGate G Row}
    (h : gate.Bridges) : gate.NeutralGlues :=
  neutralHolonomy_of_exists_isExactBridge h

/-- **Adapter, main equivalence.**  On this record the exact bridge exists
exactly when the charge glues in both orientations.  The full-support
hypothesis is discharged by the record's own witness. -/
theorem bridges_iff_hasBothOrientationsAt (gate : NodeAccountBridgeGate G Row) :
    gate.Bridges ↔ gate.HasBothOrientationsAt :=
  exists_isExactBridge_iff_hasBothOrientations gate.hasFullSupportCirculation

/-- The same equivalence in cycle form. -/
theorem bridges_iff_neutralGlues (gate : NodeAccountBridgeGate G Row) :
    gate.Bridges ↔ gate.NeutralGlues :=
  (gate.bridges_iff_hasBothOrientationsAt).trans
    gate.hasBothOrientationsAt_iff_neutralGlues

/-- The bridge gate refines the gluing gate: bridging implies gluing. -/
theorem glues_of_bridges {gate : NodeAccountBridgeGate G Row}
    (h : gate.Bridges) : gate.toNodeGluingGate.Glues :=
  ((neutralHolonomy_iff_zeroHolonomy_pair _ _ _).mp (neutralGlues_of_bridges h)).1

/-- Gluing failure forces bridge failure. -/
theorem not_bridges_of_not_glues {gate : NodeAccountBridgeGate G Row}
    (h : ¬ gate.toNodeGluingGate.Glues) : ¬ gate.Bridges :=
  fun hb => h (glues_of_bridges hb)

/-- The gate verdict. -/
def verdict (gate : NodeAccountBridgeGate G Row) : GateVerdict :=
  @verdictOf gate.Bridges (Classical.propDecidable _)

@[simp] theorem verdict_eq_pass_iff (gate : NodeAccountBridgeGate G Row) :
    gate.verdict = GateVerdict.pass ↔ gate.Bridges :=
  @verdictOf_eq_pass_iff gate.Bridges (Classical.propDecidable _)

@[simp] theorem verdict_eq_fail_iff (gate : NodeAccountBridgeGate G Row) :
    gate.verdict = GateVerdict.fail ↔ ¬ gate.Bridges :=
  @verdictOf_eq_fail_iff gate.Bridges (Classical.propDecidable _)

/-- **The dispatcher dichotomy for the bridge gate.** -/
theorem bridges_or_not_bridges (gate : NodeAccountBridgeGate G Row) :
    gate.Bridges ∨ ¬ gate.Bridges := em _

/-- **Falsifier preservation.**  A row system whose only circulation is the
zero flow admits *no* bridge gate at all: the record's positivity witness
cannot exist.  This is the `ParallelRows` separation, transported to nodes —
it is why the full-support datum is carried and not assumed. -/
theorem noGate_of_circulation_eq_zero [Nonempty Row] {node : DeclaredTargetNode G}
    (rows : NodeFlowRows node Row)
    (hzero : ∀ x : Row → ℝ, IsCirculation rows.src rows.transition x → x = 0) :
    ¬ ∃ gate : NodeAccountBridgeGate G Row,
        gate.rows.src = rows.src ∧ gate.rows.transition = rows.transition := by
  rintro ⟨gate, hsrc, htrans⟩
  obtain ⟨r⟩ := ‹Nonempty Row›
  have hcirc : IsCirculation rows.src rows.transition gate.witness := by
    rw [← hsrc, ← htrans]
    exact gate.witness_isCirculation
  have hz := congrFun (hzero _ hcirc) r
  have hpos := gate.witness_pos r
  simp only [Pi.zero_apply] at hz
  linarith

end NodeAccountBridgeGate

/-! ## Gate 3: the owner-custody (typed lifting) gate -/

/-- **The owner-custody gate at a declared-target node.**

The boundary-target index type of the typed cell is fixed to be the player type
`ι`, so the cell's target coordinates *are* the payoff coordinates of the
node's declared target.  The field `target_memFull` is the coherence: the
declared target is a feasible point of the full typed system, at the supplied
internal vector.  That single field is exactly the feasibility hypothesis of
`hasTypedLift_iff_validOnVisible_of_full`, so the Farkas adapter below needs no
side condition. -/
structure NodeCustodyGate (G : StochasticGame ι)
    [Fintype G.State] [DecidableEq G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
    (E N U Y : Type) [Fintype Y] where
  /-- The declared-target node the gate sits at. -/
  node : DeclaredTargetNode G
  /-- The typed finite cell, with boundary target coordinates equal to `ι`. -/
  cell : TypedCell ι E N U Y ι
  /-- The internal vector at which the declared target is realized. -/
  internal : Y → ℝ
  /-- **Coherence.**  The node's declared target is a feasible point of the
  full typed system. -/
  target_memFull : MemFull cell internal node.target

namespace NodeCustodyGate

variable {E N U Y : Type} [Fintype Y]

/-- The declared target is feasible in every owner's visible relaxation. -/
theorem target_memVisible (gate : NodeCustodyGate G E N U Y) (i : ι) :
    MemVisible gate.cell i gate.internal gate.node.target :=
  memVisible_of_memFull gate.target_memFull i

/-- Feasibility of owner `i`'s relaxation, in the shape the Farkas
characterization consumes. -/
theorem exists_memVisible (gate : NodeCustodyGate G E N U Y) (i : ι) :
    ∃ y t, MemVisible gate.cell i y t :=
  ⟨gate.internal, gate.node.target, gate.target_memVisible i⟩

section FiniteCell

variable [Fintype E] [Fintype N] [Fintype U]

/-- **The gate-pass proposition.**  The inequality `α · t ≤ β` on the declared
target coordinates has an `i`-typed Bellman lift. -/
def Lifts (gate : NodeCustodyGate G E N U Y) (i : ι) (α : ι → ℝ) (β : ℝ) : Prop :=
  HasTypedLift gate.cell i α β

/-- The dual datum: validity of `α · t ≤ β` on owner `i`'s visible
relaxation. -/
def ValidVisible (gate : NodeCustodyGate G E N U Y) (i : ι) (α : ι → ℝ)
    (β : ℝ) : Prop :=
  ValidOnVisible gate.cell i α β

/-- Validity on the full typed system, for contrast with `ValidVisible`. -/
def ValidFull (gate : NodeCustodyGate G E N U Y) (α : ι → ℝ) (β : ℝ) : Prop :=
  ValidOnFull gate.cell α β

/-- **Adapter, at a node.**  A one-line consumer of
`hasTypedLift_iff_validOnVisible_of_full`, unconditional thanks to the
`target_memFull` coherence field. -/
theorem lifts_iff_validVisible (gate : NodeCustodyGate G E N U Y) (i : ι)
    (α : ι → ℝ) (β : ℝ) : gate.Lifts i α β ↔ gate.ValidVisible i α β :=
  hasTypedLift_iff_validOnVisible gate.cell i α β (gate.exists_memVisible i)

/-- A typed lift is in particular valid on the full system. -/
theorem validFull_of_lifts {gate : NodeCustodyGate G E N U Y} {i : ι}
    {α : ι → ℝ} {β : ℝ} (h : gate.Lifts i α β) : gate.ValidFull α β :=
  validOnFull_of_hasTypedLift h

/-- **The declared-target self-bound.**  Owner `i` certifies the load `α` puts
on the node's own declared target vector.  This is the natural node-level
instance of the typed lifting question. -/
def LiftsTargetLoad (gate : NodeCustodyGate G E N U Y) (i : ι) (α : ι → ℝ) : Prop :=
  gate.Lifts i α (dot α gate.node.target)

/-- Adapter for the declared-target self-bound. -/
theorem liftsTargetLoad_iff_validVisible (gate : NodeCustodyGate G E N U Y)
    (i : ι) (α : ι → ℝ) :
    gate.LiftsTargetLoad i α ↔ gate.ValidVisible i α (dot α gate.node.target) :=
  gate.lifts_iff_validVisible i α _

end FiniteCell

/-- The owner-`i` custody map evaluated at the node's declared target: the
boundary information owner `i`'s own rows can see about it. -/
def targetCustody (gate : NodeCustodyGate G E N U Y) (i : ι) : U → ℝ :=
  custody gate.cell i gate.node.target

/-- The declared target is invisible to owner `i`'s custody map. -/
def IsTargetCustodyInvisible (gate : NodeCustodyGate G E N U Y) (i : ι) : Prop :=
  gate.targetCustody i = 0

/-- Custody invisibility of the declared target means none of owner `i`'s own
rows loads it. -/
theorem dot_S_target_eq_zero_of_invisible {gate : NodeCustodyGate G E N U Y}
    {i : ι} (h : gate.IsTargetCustodyInvisible i) {u : U}
    (hu : gate.cell.ownerOf u = i) : dot (gate.cell.S u) gate.node.target = 0 :=
  dot_S_eq_zero_of_custody_eq_zero h hu

section FiniteCell

variable [Fintype E] [Fintype N] [Fintype U]

/-- **The typed falsifier at a node.**  A charged recession direction of owner
`i`'s visible relaxation kills every `i`-typed lift, at every bound. -/
structure VisibleEscape (gate : NodeCustodyGate G E N U Y) (i : ι)
    (α : ι → ℝ) : Type where
  /-- The internal direction. -/
  internalDir : Y → ℝ
  /-- The boundary-target direction. -/
  targetDir : ι → ℝ
  /-- The pair is a recession direction of owner `i`'s visible relaxation. -/
  isRecession : IsVisibleRecession gate.cell i internalDir targetDir
  /-- The functional charges it strictly positively. -/
  charged : 0 < dot α targetDir

/-- A visible escape refutes the gate at **every** bound. -/
theorem not_lifts_of_visibleEscape {gate : NodeCustodyGate G E N U Y} {i : ι}
    {α : ι → ℝ} (esc : gate.VisibleEscape i α) (β : ℝ) : ¬ gate.Lifts i α β :=
  not_hasTypedLift_of_visibleRecession (gate.target_memVisible i) esc.isRecession
    esc.charged β

end FiniteCell

section FiniteCell

variable [Fintype E] [Fintype N] [Fintype U]

/-- The gate verdict. -/
def verdict (gate : NodeCustodyGate G E N U Y) (i : ι) (α : ι → ℝ) (β : ℝ) :
    GateVerdict :=
  @verdictOf (gate.Lifts i α β) (Classical.propDecidable _)

@[simp] theorem verdict_eq_pass_iff (gate : NodeCustodyGate G E N U Y) (i : ι)
    (α : ι → ℝ) (β : ℝ) :
    gate.verdict i α β = GateVerdict.pass ↔ gate.Lifts i α β :=
  @verdictOf_eq_pass_iff (gate.Lifts i α β) (Classical.propDecidable _)

@[simp] theorem verdict_eq_fail_iff (gate : NodeCustodyGate G E N U Y) (i : ι)
    (α : ι → ℝ) (β : ℝ) :
    gate.verdict i α β = GateVerdict.fail ↔ ¬ gate.Lifts i α β :=
  @verdictOf_eq_fail_iff (gate.Lifts i α β) (Classical.propDecidable _)

/-- **The dispatcher dichotomy for the custody gate.** -/
theorem lifts_or_not_lifts (gate : NodeCustodyGate G E N U Y) (i : ι)
    (α : ι → ℝ) (β : ℝ) : gate.Lifts i α β ∨ ¬ gate.Lifts i α β := em _

end FiniteCell

end NodeCustodyGate

/-! ### Vacuity probe for the custody gate -/

/-- The typed cell with no rows and no internal variables. -/
def trivialCell (ι : Type) : TypedCell ι Empty Empty Empty Empty ι where
  ownerOf := fun u => u.elim
  A := fun e => e.elim
  R := fun e => e.elim
  b := fun e => e.elim
  C := fun n => n.elim
  Q := fun n => n.elim
  c := fun n => n.elim
  B := fun u => u.elim
  S := fun u => u.elim
  d := fun u => u.elim

/-- The custody gate interface is inhabited at every declared-target node. -/
def trivialCustodyGate (node : DeclaredTargetNode G) :
    NodeCustodyGate G Empty Empty Empty Empty where
  node := node
  cell := trivialCell ι
  internal := fun y => y.elim
  target_memFull := ⟨fun e => e.elim, fun n => n.elim, fun u => u.elim⟩

/-- **Vacuity probe, pass side.**  The trivial gate lifts the zero functional
at bound `0`. -/
theorem trivialCustodyGate_lifts_zero (node : DeclaredTargetNode G) (i : ι) :
    (trivialCustodyGate node).Lifts i 0 0 := by
  refine ⟨fun e => e.elim, fun n => n.elim, fun u => u.elim, ?_⟩
  exact
    { neutral_nonneg := fun n => n.elim
      owner_nonneg := fun u => u.elim
      owner_pure := fun u => u.elim
      internal_cancel := fun v => v.elim
      boundary_load := fun w => by simp
      rhs_bound := by simp }

/-- **Vacuity probe, fail side.**  The trivial gate lifts *no* nonzero
functional, at any bound: the interface is inhabited but the gate is not
automatically passed. -/
theorem trivialCustodyGate_not_lifts_of_ne_zero (node : DeclaredTargetNode G)
    (i : ι) {α : ι → ℝ} (hα : α ≠ 0) (β : ℝ) :
    ¬ (trivialCustodyGate node).Lifts i α β := by
  rintro ⟨η, ν, μ, hlift⟩
  refine hα (funext fun w => ?_)
  have h := hlift.boundary_load w
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h
  simpa using h.symm

/-! ## Instantiation: the pure-externality cycle -/

namespace PureExternalityCycleGates

open PureExternalityCycle (game Player stagePayoffOf oneGerm prescribedGerm)
open PureExternalityCycleHolonomy
  (rowSrc rowOwner rowTransition rowAction mixedCertificate)

/-- The empty processed span of a germ of the pure-externality cycle. -/
abbrev emptySpan (germ : game.AnalyticBellmanGerm) :
    germ.EndpointHarmonicJetSpan :=
  AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty germ

/-! ### Three nodes -/

/-- The node at the prescribed germ, declaring its endpoint value `(0, 0)`. -/
def prescribedNode : DeclaredTargetNode game :=
  DeclaredTargetNode.declare prescribedGerm (emptySpan prescribedGerm)
    PureExternalityCycle.x PureExternalityCycleHolonomy.target

/-- The node at the constant-`1` germ, declaring its endpoint value `(1, 1)`. -/
def oneNode : DeclaredTargetNode game :=
  DeclaredTargetNode.declare oneGerm (emptySpan oneGerm) PureExternalityCycle.x
    fun _ => 1

/-- The node at the constant-`1` germ declaring the **other** certified
uniform equilibrium payoff `(0, 0)`.  It exists precisely because the node
type does not coerce the target from the endpoint value. -/
def misdeclaredOneNode : DeclaredTargetNode game :=
  DeclaredTargetNode.declare oneGerm (emptySpan oneGerm) PureExternalityCycle.x
    PureExternalityCycleHolonomy.target

theorem prescribedNode_isEndpointDeclared : prescribedNode.IsEndpointDeclared := by
  have h : prescribedGerm.endpointValue = fun _ _ => (0 : ℝ) :=
    PureExternalityCycle.prescribedGerm_endpointValue
  have hgoal : PureExternalityCycleHolonomy.target =
      prescribedGerm.endpointValue PureExternalityCycle.x := by
    rw [h]
    rfl
  exact hgoal

theorem oneNode_isEndpointDeclared : oneNode.IsEndpointDeclared := by
  have h : oneGerm.endpointValue = fun _ _ => (1 : ℝ) :=
    PureExternalityCycle.oneGerm_endpointValue
  have hgoal : (fun _ => (1 : ℝ) : Payoff Player) =
      oneGerm.endpointValue PureExternalityCycle.x := by
    rw [h]
  exact hgoal

/-- **The explicit non-lemma, machine-checked.**  The declared target is not
coerced from the germ's endpoint value: at `misdeclaredOneNode` the two
differ. -/
theorem misdeclaredOneNode_not_isEndpointDeclared :
    ¬ misdeclaredOneNode.IsEndpointDeclared := by
  intro hEq
  have h : PureExternalityCycleHolonomy.target =
      oneGerm.endpointValue PureExternalityCycle.x := hEq
  have h1 : oneGerm.endpointValue = fun _ _ => (1 : ℝ) :=
    PureExternalityCycle.oneGerm_endpointValue
  rw [h1] at h
  have hx := congrFun h PureExternalityCycle.x
  norm_num [PureExternalityCycleHolonomy.target] at hx

/-- There really are declared-target nodes that are not endpoint-declared. -/
theorem exists_not_isEndpointDeclared :
    ∃ node : DeclaredTargetNode game, ¬ node.IsEndpointDeclared :=
  ⟨misdeclaredOneNode, misdeclaredOneNode_not_isEndpointDeclared⟩

/-! ### The tagged rows, at any node of the cycle -/

/-- The two tagged unilateral deviation rows of the pure-externality cycle,
read at an arbitrary declared-target node.  Rows, sources, owners and
transitions are exactly `PureExternalityCycleHolonomy`'s tagged-row reading;
the gross gain is the deviating owner's own stage payoff on their deviation
row, the quantity that file also reads off the payoff table by hand. -/
def cycleRows (node : DeclaredTargetNode game) : NodeFlowRows node Bool where
  src := rowSrc
  transition := rowTransition
  ownerOf := rowOwner
  grossGain := fun b => stagePayoffOf (rowSrc b) (rowOwner b) (rowAction b)
  stochastic := PureExternalityCycleHolonomy.isStochastic_rowTransition
  entry_isSource := ⟨node.entry, rfl⟩

/-- At the prescribed node the derived charge is literally
`PureExternalityCycleHolonomy.rowCharge`. -/
theorem cycleRows_prescribed_charge :
    (cycleRows prescribedNode).charge = PureExternalityCycleHolonomy.rowCharge :=
  rfl

/-- At the constant-`1` node the derived charge vanishes: the declared target
`(1, 1)` exactly absorbs every deviation row's own stage payoff. -/
theorem cycleRows_one_charge : (cycleRows oneNode).charge = 0 := by
  funext b
  cases b <;>
    norm_num [NodeFlowRows.charge, cycleRows, oneNode, DeclaredTargetNode.declare,
      rowSrc, rowOwner, rowAction, stagePayoffOf, TwoCycle.src, TwoCycle.ownerOf]

/-- **Germ coherence holds for the tagged rows.**  The row transitions
reproduce the germ's endpoint pure-deviation state kernels: in this game the
transition ignores every action, so the kernel is the point mass on the flipped
state whatever the profile and whatever the deviation. -/
theorem cycleRows_isEndpointKernelTagged (node : DeclaredTargetNode game) :
    (cycleRows node).IsEndpointKernelTagged fun r => rowAction r := by
  intro r w
  rw [game.expect_finkPureDeviationStateKernel_eq]
  have hinner : ∀ a : game.JointAct,
      expect (game.transition ((cycleRows node).src r) a) w =
        w (!((cycleRows node).src r)) := by
    intro a
    rw [PureExternalityCycle.transition_eq, expect_pure]
  simp_rw [hinner]
  rw [expect_const]
  cases r <;>
    norm_num [cycleRows, rowSrc, rowTransition, TwoCycle.src, TwoCycle.transition,
      Fintype.sum_bool]

/-- **Germ coherence is refutable.**  The self-loop row system at the
prescribed node is *not* endpoint-kernel tagged: the game's kernel flips the
state, the self-loop does not. -/
theorem selfLoopRows_not_isEndpointKernelTagged :
    ¬ (NodeFlowRows.selfLoopRows prescribedNode false).IsEndpointKernelTagged
        fun _ => false := by
  intro h
  have hx : prescribedNode.entry = PureExternalityCycle.x := rfl
  have hkey := h () fun v => if v = PureExternalityCycle.x then (1 : ℝ) else 0
  rw [game.expect_finkPureDeviationStateKernel_eq] at hkey
  have hinner : ∀ a : game.JointAct,
      expect (game.transition ((NodeFlowRows.selfLoopRows prescribedNode false).src ())
        a) (fun v => if v = PureExternalityCycle.x then (1 : ℝ) else 0) =
        (if (!PureExternalityCycle.x) = PureExternalityCycle.x then (1 : ℝ) else 0) := by
    intro a
    rw [show (NodeFlowRows.selfLoopRows prescribedNode false).src () =
      PureExternalityCycle.x from hx, PureExternalityCycle.transition_eq, expect_pure]
  simp_rw [hinner] at hkey
  rw [expect_const] at hkey
  norm_num [NodeFlowRows.selfLoopRows, hx, PureExternalityCycle.x,
    Fintype.sum_bool] at hkey

/-! ### The gluing gates -/

/-- The gluing gate at the prescribed node. -/
def prescribedGluingGate : NodeGluingGate game Bool :=
  NodeGluingGate.of (cycleRows prescribedNode)

/-- The gluing gate at the constant-`1` node. -/
def oneGluingGate : NodeGluingGate game Bool :=
  NodeGluingGate.of (cycleRows oneNode)

/-- **Gate failure at the prescribed node.**  The declared target `(0, 0)`
leaves both deviation rows charged `1`, and the mixed certificate is the exact
Farkas witness. -/
theorem prescribedGluingGate_not_glues : ¬ prescribedGluingGate.Glues :=
  PureExternalityCycleHolonomy.mixedCertificate_not_zeroHolonomy

/-- No scalar account potential discharges the prescribed node's charges. -/
theorem prescribedGluingGate_not_hasAccountPotential :
    ¬ prescribedGluingGate.HasAccountPotential := fun h =>
  prescribedGluingGate_not_glues
    ((prescribedGluingGate.glues_iff_hasAccountPotential).mpr h)

theorem prescribedGluingGate_verdict :
    prescribedGluingGate.verdict = GateVerdict.fail :=
  (NodeGluingGate.verdict_eq_fail_iff _).mpr prescribedGluingGate_not_glues

/-- The typed falsifier is present at the prescribed node. -/
theorem nonempty_prescribed_farkasWitness :
    Nonempty prescribedGluingGate.FarkasWitness :=
  (prescribedGluingGate.nonempty_farkasWitness_iff_not_glues).mpr
    prescribedGluingGate_not_glues

/-- **Gate success at the constant-`1` node.**  The declared target `(1, 1)`
zeroes every row charge. -/
theorem oneGluingGate_glues : oneGluingGate.Glues :=
  zeroHolonomy_of_charge_nonpos fun r => by
    change (cycleRows oneNode).charge r ≤ 0
    rw [cycleRows_one_charge]
    simp

theorem oneGluingGate_hasAccountPotential : oneGluingGate.HasAccountPotential :=
  (oneGluingGate.glues_iff_hasAccountPotential).mp oneGluingGate_glues

theorem oneGluingGate_verdict : oneGluingGate.verdict = GateVerdict.pass :=
  (NodeGluingGate.verdict_eq_pass_iff _).mpr oneGluingGate_glues

/-! ### The account-bridge gates -/

/-- The account-bridge gate at the prescribed node.  The full-support witness
is the mixed certificate `(1/2, 1/2)`. -/
def prescribedBridgeGate : NodeAccountBridgeGate game Bool where
  toNodeGluingGate := prescribedGluingGate
  witness := mixedCertificate
  witness_isCirculation :=
    PureExternalityCycleHolonomy.isNormalizedCirculation_mixedCertificate.toIsCirculation
  witness_pos := fun _ => by norm_num [mixedCertificate, TwoCycle.uniform]

/-- The account-bridge gate at the constant-`1` node, with the same witness. -/
def oneBridgeGate : NodeAccountBridgeGate game Bool where
  toNodeGluingGate := oneGluingGate
  witness := mixedCertificate
  witness_isCirculation :=
    PureExternalityCycleHolonomy.isNormalizedCirculation_mixedCertificate.toIsCirculation
  witness_pos := fun _ => by norm_num [mixedCertificate, TwoCycle.uniform]

/-- **Bridge failure at the prescribed node**, even though the full-support
witness is present: this is an orientation-free failure, inherited from the
one-sided gluing failure. -/
theorem prescribedBridgeGate_not_bridges : ¬ prescribedBridgeGate.Bridges :=
  NodeAccountBridgeGate.not_bridges_of_not_glues prescribedGluingGate_not_glues

theorem prescribedBridgeGate_verdict :
    prescribedBridgeGate.verdict = GateVerdict.fail :=
  (NodeAccountBridgeGate.verdict_eq_fail_iff _).mpr prescribedBridgeGate_not_bridges

/-- **Bridge success at the constant-`1` node**: the zero charge is the exact
drift of the zero potential. -/
theorem oneBridgeGate_bridges : oneBridgeGate.Bridges := by
  refine ⟨0, ?_⟩
  have hc : oneBridgeGate.rows.charge = 0 := cycleRows_one_charge
  rw [hc]
  exact isExactBridge_zero _ _

theorem oneBridgeGate_verdict : oneBridgeGate.verdict = GateVerdict.pass :=
  (NodeAccountBridgeGate.verdict_eq_pass_iff _).mpr oneBridgeGate_bridges

/-- The two-sided cycle criterion at the constant-`1` node. -/
theorem oneBridgeGate_neutralGlues : oneBridgeGate.NeutralGlues :=
  NodeAccountBridgeGate.neutralGlues_of_bridges oneBridgeGate_bridges

/-! ### The custody gate -/

/-- The owner-custody gate at the prescribed node.  The typed cell is the
two-owner cross-cancellation system: `Ω = T = Player`, one
internal variable, one owner-neutral row, and one unilateral row per owner.
The coherence field checks that the declared target `(0, 0)` is a feasible
point of the full typed system. -/
def prescribedCustodyGate : NodeCustodyGate game Empty Unit Bool Unit where
  node := prescribedNode
  cell := CrossOwnerCancellation.system
  internal := fun _ => 0
  target_memFull := CrossOwnerCancellation.memFull_zero

/-- **Custody gate failure, both owners, every bound.**  The cross-owner
normal `(1, 1)` is valid on the full typed system yet has no typed lift for
either owner: the coordinate the owner does not control escapes inside that
owner's relaxation while staying invisible to their custody map. -/
theorem prescribedCustodyGate_not_lifts (i : Player) (β : ℝ) :
    ¬ prescribedCustodyGate.Lifts i CrossOwnerCancellation.crossNormal β :=
  CrossOwnerCancellation.not_hasTypedLift i β

theorem prescribedCustodyGate_verdict (i : Player) (β : ℝ) :
    prescribedCustodyGate.verdict i CrossOwnerCancellation.crossNormal β =
      GateVerdict.fail :=
  (NodeCustodyGate.verdict_eq_fail_iff _ _ _ _).mpr
    (prescribedCustodyGate_not_lifts i β)

/-- Yet the same functional is valid on the full typed system: the gate failure
is custody, not infeasibility. -/
theorem prescribedCustodyGate_validFull :
    prescribedCustodyGate.ValidFull CrossOwnerCancellation.crossNormal 0 :=
  CrossOwnerCancellation.validOnFull

/-- **Custody gate success on an owned coordinate.**  Owner `false`'s own
target row is liftable by owner `false`. -/
theorem prescribedCustodyGate_lifts_ownNormal :
    prescribedCustodyGate.Lifts false (CrossOwnerCancellation.ownNormal false) 0 :=
  CrossOwnerCancellation.hasTypedLift_ownNormal

theorem prescribedCustodyGate_verdict_ownNormal :
    prescribedCustodyGate.verdict false (CrossOwnerCancellation.ownNormal false) 0 =
      GateVerdict.pass :=
  (NodeCustodyGate.verdict_eq_pass_iff _ _ _ _).mpr
    prescribedCustodyGate_lifts_ownNormal

/-- The escape direction is invisible to owner `i`'s custody map, evaluated at
the node's declared target's coordinate system. -/
theorem prescribedCustodyGate_custody_escape (i : Player) :
    custody prescribedCustodyGate.cell i (CrossOwnerCancellation.escape i) = 0 :=
  CrossOwnerCancellation.custody_escape i

/-- The typed falsifier at the node: a charged visible escape for each owner. -/
def prescribedCustodyGate_escape (i : Player) :
    prescribedCustodyGate.VisibleEscape i CrossOwnerCancellation.crossNormal where
  internalDir := fun _ => 0
  targetDir := CrossOwnerCancellation.escape i
  isRecession := CrossOwnerCancellation.isVisibleRecession_escape i
  charged := by
    rw [CrossOwnerCancellation.dot_crossNormal_escape]
    norm_num

/-! ### Capstone -/

/-- **Capstone: the leaf-facing gate data of the pure-externality cycle.**

Two declared-target nodes over the same game, both *endpoint-declared*, carry
the same tagged owner-labeled row system and land on opposite sides of every
flow gate; a third node shows the declared target is not coerced from the
endpoint value; and the custody gate reproduces the cross-owner-cancellation
falsifier at a node while still passing on an owned coordinate.

Read together with `PureExternalityCycleHolonomy.routeZero_acceptance` — which
certifies that the prescribed profile *does* deliver `(0, 0)` as a uniform
equilibrium payoff — this says exactly that a failed gate is not an
obstruction to equilibrium.  The gates are leaf data, not verdicts on the
game. -/
theorem declaredTargetLeafGates_acceptance :
    (prescribedNode.IsEndpointDeclared ∧ oneNode.IsEndpointDeclared ∧
        ¬ misdeclaredOneNode.IsEndpointDeclared) ∧
      (¬ prescribedGluingGate.Glues ∧
        ¬ prescribedGluingGate.HasAccountPotential ∧
        Nonempty prescribedGluingGate.FarkasWitness ∧
        prescribedGluingGate.verdict = GateVerdict.fail) ∧
      (oneGluingGate.Glues ∧ oneGluingGate.HasAccountPotential ∧
        oneGluingGate.verdict = GateVerdict.pass) ∧
      (¬ prescribedBridgeGate.Bridges ∧ oneBridgeGate.Bridges) ∧
      ((∀ i : Player, ∀ β : ℝ,
          ¬ prescribedCustodyGate.Lifts i CrossOwnerCancellation.crossNormal β) ∧
        prescribedCustodyGate.ValidFull CrossOwnerCancellation.crossNormal 0 ∧
        prescribedCustodyGate.Lifts false
          (CrossOwnerCancellation.ownNormal false) 0) ∧
      (∀ node : DeclaredTargetNode game,
        (cycleRows node).IsEndpointKernelTagged fun r => rowAction r) :=
  ⟨⟨prescribedNode_isEndpointDeclared, oneNode_isEndpointDeclared,
      misdeclaredOneNode_not_isEndpointDeclared⟩,
    ⟨prescribedGluingGate_not_glues, prescribedGluingGate_not_hasAccountPotential,
      nonempty_prescribed_farkasWitness, prescribedGluingGate_verdict⟩,
    ⟨oneGluingGate_glues, oneGluingGate_hasAccountPotential, oneGluingGate_verdict⟩,
    ⟨prescribedBridgeGate_not_bridges, oneBridgeGate_bridges⟩,
    ⟨prescribedCustodyGate_not_lifts, prescribedCustodyGate_validFull,
      prescribedCustodyGate_lifts_ownNormal⟩,
    cycleRows_isEndpointKernelTagged⟩

end PureExternalityCycleGates

end StateDecidable

end StochasticGame
end GameTheory

end
