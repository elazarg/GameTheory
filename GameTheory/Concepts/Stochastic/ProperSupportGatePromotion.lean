/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralOccupationBehaviorRealization
import GameTheory.Concepts.Stochastic.PublicRecurrentClassTarget
import Math.Probability.OccupationFlowAlternative

/-!
# The five-gate proper-support promotion bundle (easy direction)

A strict analytic support inclusion `supp_A(C) ⊊ A` is a *routing signal*, not
a child-construction theorem.  The canonical proper-support promotion theorem
is a **relative** statement: the promoted whole-target child exists exactly
when five independent finite gates hold for one and the same cell-labelled
child datum.

This file bundles those five gates as named structures and proves the **easy
direction**: the bundle produces the promotion output.  The promotion output
is the existing `PublicRecurrentClassChild` — a canonical child carrying the
parent's *whole* payoff-vector target together with strict rank descent — plus
the remaining components of the output tuple.

## The five gates, verbatim

1. **Common support realization.**  All rows on `C` are realized
   simultaneously by one public behavioral profile and one total update rule;
   the analytic circulation lifts to an actual invariant occupation on the
   resulting owner-labelled public product.
   → `CommonSupportRealization` (built on `CommonProfileRowRealization`).
2. **Complete target compatibility.**  A complete child target and target
   field satisfy the recurrent identities, every owner-labelled Bellman
   inequality, the parent target-balance equations, and the exact
   target/rebasing fibers, all in the same realization cell.
   → `CompleteTargetCompatibility`.
3. **Robust finite entry synthesis.**  A parent-to-boundary target field, bias
   potentials, neutral-occupation inequalities, total updates, exact boundary
   maps, and explicit nonentry fallbacks satisfy the entry conditions.
   → `RobustFiniteEntry`.
4. **Target-constrained germ coherence.**  The child datum is the restriction
   of the parent germ, or is supplied by a restarted target-constrained germ
   with a compatible interface, or by a controlled all-accuracy approximation.
   → `TargetConstrainedGermCoherence`.
5. **Hereditary intrinsic progress.**  After minimal strategic closure and
   canonical bisimulation quotient, every reachable descendant of the child has
   strictly smaller canonical global rank than the parent.
   → `HereditaryIntrinsicProgress`.

`FiveGateData` bundles all five; `FiveGateData.promote` and
`FiveGateData.output` are the easy direction.

## Honest status of each gate

* **Gate 1 is faithful and partly banked.**  The realization equations are
  written at the level of the actual game: *one* state-indexed product profile
  `prescribed` occurs in the prescribed row and in every response row, which is
  exactly the answer's decisive compatibility condition (its equation (8) is
  enforced by using the same variable, not by a side equation).  The existing
  development discharges precisely this half:
  `AnalyticBellmanGerm.fixedOccupationActionDist_bind_transition`
  (`PlayerNeutralOccupationBehaviorRealization.lean`) is definitionally the
  `rows_realized` field, and `finkStateKernel` is definitionally the realized
  prescribed kernel; see `CommonProfileRowRealization.ofFinkActiveOccupation`.
  The occupation lift (the answer's (10)–(11)) and the closed reachable class
  are *not* supplied by that development and stay as fields.
* **Gate 2 is faithful** for the answer's displayed finite system: the
  whole-target conditions (17), the recurrent identity (19), the owner-labelled
  Bellman inequality (20) with one potential per owner and one multiplier per
  owner, the child entry target (15), and the parent target balance.  The
  remaining clauses of the answer's witness set (22) — exact target/rebasing
  fibers, account resets, owner-history compatibility, canonical face — are
  *not* modelled; they are collected in one neutral socket `CellFiber`, which
  is trivially satisfiable when instantiated by `fun _ => True`.  That is an
  explicit gap, not a claim.
* **Gate 3 is faithful** for (27), (28), (32), (33), the `Z = E ⊔ B ⊔ F`
  decomposition and the *deterministic-bound* form of the stopping condition
  (the answer's third and strongest stopping variant: acyclicity of the
  positive-support graph inside `E`, here witnessed by a strictly decreasing
  `exitRank`).  The martingale/supermartingale delivery (37) and the entry-debt
  bound (35)–(36) are **not** derived; they need stopped-process machinery.
  What *is* derived here: no reachable closed prescribed class inside `E`
  (`no_closed_class_in_continuing`), no deviation self-loop inside `E`
  (`no_deviation_selfLoop`, which is exactly the answer's entry
  counterexample (39)), and the exact neutral-occupation condition (31) from
  the finite dual (32) (`neutralOccupation_charge_nonpos`).
* **Gate 4 is faithful only for the inherited/restarted alternatives**:
  the endpoint equation (41)/(42) and the interface commutation (40), stated
  over neutral type parameters because the tree has no analytic restriction
  map on germs.  The controlled all-accuracy approximation (43), with its
  residual moduli and approximation calendar, is **omitted**.
* **Gate 5 is faithful** to the hereditary formulation, with the descendant
  relation, the node rank, and the rank order left as parameters (the tree's
  `AnalyticEndpointLexRank`/`AnalyticEndpointDeflationRank` are legal
  instantiations).  The reflexivity field `self_descendant` is load-bearing;
  see `hereditaryProgress_descends_vacuous_without_self`.

## Gates 4 and 5 are components of the conclusion

The answer states this itself: *"Germ coherence and strict global progress are
components of the tuple itself."*  Consequently the easy direction is genuinely
contentful only for gates 1–3 (which manufacture the child, its whole target,
and its legal entry); gate 4 is carried through unchanged and gate 5 is
instantiated at the child.  No gate field is literally the conclusion:
`target child = target parent` is *derived* from gate 2's harmonicity by
`ReachableClosedClass.harmonicVector_eq_entry`, and `rankLt (rank child)
(rank parent)` is obtained from gate 5 by `∀`-instantiation at the child.

## Falsifier probes

Every new `Prop`/structure was checked against a trivial witness:

* `CommonSupportRealization.classRows_nonempty` — the zero occupation cannot
  satisfy gate 1: normalization plus the support equivalence (11) forces the
  class row set to be nonempty.
* `no_deviation_selfLoop`, `no_closed_class_in_continuing` — gate 3 is not
  satisfied by the answer's entry counterexample (39), where `U ≡ 0` verifies
  (28) yet a deviator stays forever.
* `CompleteTargetCompatibility.recurrent_charge_coboundary` — with a zero
  target field, gate 2 still forces the prescribed payoff to be an exact
  coboundary of the bias, i.e. mean charge zero on every recurrent class
  (the answer's (21)).  The zero witness is therefore admissible only for a
  game with zero recurrent payoff, which is correct.
* `hereditaryProgress_descends_vacuous_without_self` — the `descends` field
  alone is satisfied by the empty descendant relation while the conclusion
  fails; this is why `self_descendant` is a field.
* `germEndpoint_not_sufficient` — the answer's Part D counterexample: two child
  germs with the same endpoint vector and different strategic interfaces.  The
  endpoint field of gate 4 alone does not imply the commutation field.
* The neutral socket `CellFiber` *is* vacuous under `fun _ => True`; that is
  documented above as a gap rather than a modelled condition.

## What this file does not do

The converse (a successful promotion supplies the five gates) is not proved.
The two rank counterexamples of Part E (redundant support; reactivation under
closure) are not formalized here; they bear on the converse and on whether
gate 5 can be *derived* from proper support, which it cannot.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace ProperSupportGatePromotion

open Math Math.PMFProduct Math.Probability Set

/-! ## Gate 1: common support realization -/

section GateOne

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : StochasticGame ι)
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {Row : Type}

/-- One common public behavioral profile realizing the prescribed row and
every response row.

This is the decisive half of the answer's Part A.  The prescribed row (6) and
each response row (7) are produced by *the same* state-indexed product profile
`prescribed`; the answer's compatibility equation (8) is therefore not a side
condition but is enforced by the shared variable.  A response row differs from
the prescribed row only in the owner's own coordinate, which is replaced by the
row's own action `α^r`. -/
structure CommonProfileRowRealization
    (rowOwner : Row → ι) (rowSource : Row → G.State)
    (rowKernel : Row → PMF G.State)
    (prescribedKernel : G.State → PMF G.State) where
  /-- The one prescribed public behavioral profile `σ^x`. -/
  prescribed : G.State → ∀ k, PMF (G.Act k)
  /-- The response action `α^r ∈ Δ(A_{i(r)})` of each row's owner. -/
  rowAction : ∀ r : Row, PMF (G.Act (rowOwner r))
  /-- Equation (6): the prescribed profile realizes the prescribed kernel. -/
  prescribed_realized :
    ∀ x : G.State,
      (pmfPi (prescribed x)).bind (G.transition x) = prescribedKernel x
  /-- Equation (7) with (8) built in: every response row is realized by the
  same opponents' mixtures. -/
  rows_realized :
    ∀ r : Row,
      (pmfPi
          (Function.update (prescribed (rowSource r)) (rowOwner r)
            (rowAction r))).bind (G.transition (rowSource r)) =
        rowKernel r

/-- **Gate 1.**  All rows on `C` are realized simultaneously by one public
behavioral profile and one total update rule, and the analytic circulation
lifts to an actual invariant occupation whose support is exactly `supp_A(C)`.

`core` records the answer's requirement that `C` be closed and reachable *in
the realized support graph*, using the existing `ReachableClosedClass`. -/
structure CommonSupportRealization [Fintype Row]
    (rowOwner : Row → ι) (rowSource : Row → G.State)
    (rowKernel : Row → PMF G.State)
    (prescribedKernel : G.State → PMF G.State)
    (classRows : Finset Row) (parentEntry : G.State)
    extends CommonProfileRowRealization G rowOwner rowSource rowKernel
      prescribedKernel where
  /-- The owner/row-labelled occupation `μ(x, r)` of (10). -/
  occupation : Row → ℝ
  /-- `μ ≥ 0`. -/
  occupation_nonneg : ∀ r : Row, 0 ≤ occupation r
  /-- Invariance in (10), written with the existing actual occupation
  column `Q_r − δ_{source r}`. -/
  occupation_balanced :
    ∀ u : G.State,
      ∑ r : Row,
        occupation r * actualOccupationColumn rowKernel rowSource r u = 0
  /-- Normalization `∑_{x,r} μ(x,r) = 1` in (10). -/
  occupation_total : ∑ r : Row, occupation r = 1
  /-- Equation (11): the realized occupation support is exactly the analytic
  support of the class. -/
  occupation_support : ∀ r : Row, 0 < occupation r ↔ r ∈ classRows
  /-- `C` is closed and reachable in the realized public kernel. -/
  core : ReachableClosedClass prescribedKernel parentEntry
  /-- The rows of `C` sit at states of `C`. -/
  classRows_source : ∀ r ∈ classRows, rowSource r ∈ core.states

namespace CommonSupportRealization

variable [Fintype Row]
  {rowOwner : Row → ι} {rowSource : Row → G.State}
  {rowKernel : Row → PMF G.State}
  {prescribedKernel : G.State → PMF G.State}
  {classRows : Finset Row} {parentEntry : G.State}

omit [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- **Falsifier probe for gate 1.**  The zero occupation cannot witness gate 1:
normalization together with the support equivalence (11) forces the class row
set to be nonempty. -/
theorem classRows_nonempty
    (data :
      CommonSupportRealization G rowOwner rowSource rowKernel
        prescribedKernel classRows parentEntry) :
    classRows.Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hzero : ∀ r : Row, data.occupation r = 0 := by
    intro r
    rcases (data.occupation_nonneg r).lt_or_eq with hpos | heq
    · exact absurd ((data.occupation_support r).1 hpos) (by simp [hempty])
    · exact heq.symm
  have htotal := data.occupation_total
  rw [Finset.sum_congr rfl fun r _ => hzero r] at htotal
  simp at htotal

end CommonSupportRealization

end GateOne

/-! ### Banking gate 1 from the existing behavioral realization

The player-neutral occupation realization already proves the whole
`CommonProfileRowRealization` half of gate 1 for the Fink-frozen profile: the
opponents keep one frozen mixed action at every state and each active
occupation index contributes its own owner action. -/

section BankGateOne

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- **Gate 1 is banked (realization half).**  For a fixed positive parameter of
an analytic Fink germ and a fixed player, the active player-neutral occupation
family is realized by *one* profile: the frozen Fink profile, with the owner's
coordinate replaced row by row.

Every field is discharged by an existing declaration:
`prescribed_realized` is definitional (`finkStateKernel` is literally the
prescribed bind), and `rows_realized` is
`AnalyticBellmanGerm.fixedOccupationActionDist_bind_transition`. -/
def CommonProfileRowRealization.ofFinkActiveOccupation
    (germ : G.AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) germ.radius) (who : ι)
    (active : Finset (germ.PlayerNeutralOccupationIndex who)) :
    CommonProfileRowRealization G
      (Row := {index : germ.PlayerNeutralOccupationIndex who //
        index ∈ active})
      (fun _ => who)
      (fun r => germ.playerNeutralOccupationSource who r.1)
      (fun r => germ.finkPlayerNeutralOccupationKernelAt ht who r.1)
      (G.finkStateKernel (germ.finkPointAt ht)) where
  prescribed := G.finkProfile (germ.finkPointAt ht)
  rowAction := AnalyticBellmanGerm.fixedOccupationActionDist germ ht who
  prescribed_realized := fun _ => rfl
  rows_realized :=
    AnalyticBellmanGerm.fixedOccupationActionDist_bind_transition
      germ ht who

omit [DecidableEq G.State] in
/-- The same one profile has an actual public state-history law, and it is
exactly the abstract mixed-row law used by the occupation account.  This is the
"one total update rule" half of gate 1, re-exported from
`realizedActiveOccupationStateHistoryLaw_eq_adaptiveHistoryLaw`. -/
theorem finkActiveOccupation_historyLaw
    (germ : G.AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) germ.radius) (who : ι) (initial : G.State)
    (active : Finset (germ.PlayerNeutralOccupationIndex who))
    (selection :
      ∀ stage, (Fin (stage + 1) → G.State) →
        PMF
          {index : germ.PlayerNeutralOccupationIndex who //
            index ∈ active})
    (source_compatible :
      ∀ stage history index,
        selection stage history index ≠ 0 →
          germ.playerNeutralOccupationSource who index.1 =
            history (Fin.last stage))
    (stage : ℕ) :
    AnalyticBellmanGerm.realizedActiveOccupationStateHistoryLaw
        germ ht who initial active selection stage =
      adaptiveHistoryLaw
        (adaptiveMarkovStep initial
          (AnalyticBellmanGerm.activeOccupationMixedStep
            germ ht who selection))
        (stage + 1) :=
  AnalyticBellmanGerm.realizedActiveOccupationStateHistoryLaw_eq_adaptiveHistoryLaw
    germ ht who initial active selection source_compatible stage

end BankGateOne

/-! ## Gate 2: complete target compatibility -/

section GateTwo

variable {ι : Type} (G : StochasticGame ι) {Row : Type}

/-- Target drift (16) of a response row `r` owned by `i(r)`:
`Δ_{i(r)}^r(X) = X_{i(r)}(x_r) − (K^r X_{i(r)})(x_r)`. -/
def targetDrift (rowOwner : Row → ι) (rowSource : Row → G.State)
    (rowKernel : Row → PMF G.State) (targetField : G.State → ι → ℝ)
    (r : Row) : ℝ :=
  targetField (rowSource r) (rowOwner r) -
    expect (rowKernel r) fun y => targetField y (rowOwner r)

/-- Average-payoff charge (18) of a response row:
`d_{i(r)}^r(X) = g_{i(r)}^r(x_r) − X_{i(r)}(x_r)`. -/
def targetCharge (rowOwner : Row → ι) (rowSource : Row → G.State)
    (rowPayoff : Row → ι → ℝ) (targetField : G.State → ι → ℝ)
    (r : Row) : ℝ :=
  rowPayoff r (rowOwner r) - targetField (rowSource r) (rowOwner r)

/-- **Gate 2.**  A complete child target *and target field* satisfying the
recurrent identities, every owner-labelled Bellman inequality, the parent
target-balance equation, and the realization-cell/fiber conditions.

The answer insists that the witness is the field `X : Q_C → ℝ^I` and not the
bare vector `w`; that is why `targetField` is a field and `childTarget` is
*defined* from it at the child entry (15).

`CellFiber` is a **neutral socket**: it stands for the clauses of the answer's
witness set (22) that this file does not model (exact target/rebasing fibers,
account resets, owner-history compatibility, canonical face).  It is vacuous
when instantiated by `fun _ => True`. -/
structure CompleteTargetCompatibility
    (rowOwner : Row → ι) (rowSource : Row → G.State)
    (rowKernel : Row → PMF G.State) (rowPayoff : Row → ι → ℝ)
    (prescribedKernel : G.State → PMF G.State)
    (prescribedPayoff : G.State → ι → ℝ)
    (classRows : Finset Row) (classStates : Finset G.State)
    (CellFiber : (G.State → ι → ℝ) → Prop)
    (parentTarget : ι → ℝ) (classEntry : G.State) where
  /-- The complete target field `X : Q_C → ℝ^I`. -/
  targetField : G.State → ι → ℝ
  /-- Equation (17), first half: `K⁰X = X` on the class. -/
  prescribed_harmonic :
    ∀ x ∈ classStates, ∀ i : ι,
      targetField x i =
        expect (prescribedKernel x) fun y => targetField y i
  /-- Parent whole-target balance: the parent's whole vector target is the
  value of the target field at the class entry. -/
  parent_balance : parentTarget = targetField classEntry
  /-- Equation (17), second half: nonnegative target drift on active rows. -/
  drift_nonneg :
    ∀ r ∈ classRows,
      0 ≤ targetDrift G rowOwner rowSource rowKernel targetField r
  /-- The prescribed bias potential `b_i^0`. -/
  biasPrescribed : ι → G.State → ℝ
  /-- Equation (19): the recurrent payoff identity in exact potential form,
  equivalently (21) zero mean charge on every closed prescribed class. -/
  recurrent_identity :
    ∀ i : ι, ∀ x ∈ classStates,
      prescribedPayoff x i - targetField x i +
          (expect (prescribedKernel x) (biasPrescribed i) -
            biasPrescribed i x) = 0
  /-- The owner bias potential `b_i`, common to every row of owner `i`. -/
  bias : ι → G.State → ℝ
  /-- The owner multiplier `λ_i`. -/
  slope : ι → ℝ
  slope_nonneg : ∀ i : ι, 0 ≤ slope i
  /-- Equation (20): the owner-labelled Bellman inequality. -/
  owner_bellman :
    ∀ r ∈ classRows,
      targetCharge G rowOwner rowSource rowPayoff targetField r +
          (expect (rowKernel r) (bias (rowOwner r)) -
            bias (rowOwner r) (rowSource r)) ≤
        slope (rowOwner r) *
          targetDrift G rowOwner rowSource rowKernel targetField r
  /-- The child entry public mode `x_C`. -/
  childEntry : G.State
  childEntry_mem : childEntry ∈ classStates
  /-- The child's whole target vector `w_C`. -/
  childTarget : ι → ℝ
  /-- Equation (15): `w = X(x_C)`. -/
  child_target_eq : childTarget = targetField childEntry
  /-- The unmodelled realization-cell / fiber clauses of (22). -/
  cell_fiber : CellFiber targetField

namespace CompleteTargetCompatibility

variable {G}
  {rowOwner : Row → ι} {rowSource : Row → G.State}
  {rowKernel : Row → PMF G.State} {rowPayoff : Row → ι → ℝ}
  {prescribedKernel : G.State → PMF G.State}
  {prescribedPayoff : G.State → ι → ℝ}
  {classRows : Finset Row} {classStates : Finset G.State}
  {CellFiber : (G.State → ι → ℝ) → Prop}
  {parentTarget : ι → ℝ} {classEntry : G.State}

/-- **Falsifier probe for gate 2.**  Even a zero target field does not make
gate 2 vacuous: the recurrent identity (19) still forces the prescribed
recurrent charge to be an exact coboundary of the prescribed bias, which is
the answer's (21).  So the zero witness is admissible only for a game whose
recurrent payoff is already a coboundary. -/
theorem recurrent_charge_coboundary
    (data :
      CompleteTargetCompatibility G rowOwner rowSource rowKernel rowPayoff
        prescribedKernel prescribedPayoff classRows classStates CellFiber
        parentTarget classEntry)
    (i : ι) (x : G.State) (hx : x ∈ classStates) :
    prescribedPayoff x i - data.targetField x i =
      data.biasPrescribed i x -
        expect (prescribedKernel x) (data.biasPrescribed i) := by
  have h := data.recurrent_identity i x hx
  linarith

end CompleteTargetCompatibility

end GateTwo

/-! ## Gate 3: robust finite entry synthesis -/

/-- **Gate 3.**  The finite parent selector arena `Z = E ⊔ B ⊔ F` together with
a complete target field `U`, bias potentials, the neutral-occupation
inequalities in finite dual form, exact two-sided prescribed delivery, and an
explicit stopping witness.

`Arena` and `DevRow` are fields rather than parameters: the selector arena is
part of the witness, not of the ambient data.  `DevRow` enumerates the answer's
unilateral rows `(z, a)`; totality of the public update is the totality of
`prescribedStep` and `devKernel`.

Faithful to (27), (28), (32), (33) and the `Z = E ⊔ B ⊔ F` decomposition.  The
stopping condition is taken in the answer's strongest listed form: the
positive-support graph inside `E` is acyclic, witnessed by a strictly
decreasing `exitRank`.  The entry-debt bound (35)–(36) and the stopped
delivery (37) are *not* fields and are not derived here. -/
structure RobustFiniteEntry (ι : Type) (parentTarget childTarget : ι → ℝ) :
    Type 1 where
  /-- The finite parent selector arena `Z`. -/
  Arena : Type
  /-- `z₀`: the parent entry history `h`. -/
  root : Arena
  /-- `E`: continuing selector modes. -/
  Continuing : Finset Arena
  /-- `B`: legal child-entry boundaries. -/
  Boundary : Finset Arena
  /-- `F`: explicitly valued nonentry terminal or fallback classes. -/
  Fallback : Finset Arena
  /-- `Z = E ∪ B ∪ F`. -/
  arena_cover : ∀ z : Arena, z ∈ Continuing ∨ z ∈ Boundary ∨ z ∈ Fallback
  continuing_not_boundary : ∀ z ∈ Continuing, z ∉ Boundary
  continuing_not_fallback : ∀ z ∈ Continuing, z ∉ Fallback
  root_continuing : root ∈ Continuing
  /-- `P⁰`: the total public update under prescribed play. -/
  prescribedStep : Arena → PMF Arena
  /-- The unilateral rows `(z, a)` of the selector arena. -/
  DevRow : Type
  devOwner : DevRow → ι
  devSource : DevRow → Arena
  /-- `P_i^a`: the total public update under a unilateral action. -/
  devKernel : DevRow → PMF Arena
  /-- `d_i(z, a)`: the selector's one-step entry-debt charge. -/
  devCharge : DevRow → ℝ
  /-- `d_i^0(z)`: the prescribed one-step entry-debt charge. -/
  prescribedCharge : Arena → ι → ℝ
  /-- The complete parent-to-boundary target field `U : Z → ℝ^I`. -/
  U : Arena → ι → ℝ
  /-- Equation (27): `U(z₀) = v`. -/
  root_value : U root = parentTarget
  /-- `w^{c(b)}`: the target of the child entered at boundary `b`. -/
  boundaryChildTarget : Arena → ι → ℝ
  /-- Equation (27): `U(b) = w^{c(b)}`. -/
  boundary_value : ∀ b ∈ Boundary, U b = boundaryChildTarget b
  /-- The boundary at which the promoted child is entered. -/
  selectedBoundary : Arena
  selectedBoundary_mem : selectedBoundary ∈ Boundary
  /-- The promoted child's whole target is delivered at the selected
  boundary. -/
  selected_child_target : boundaryChildTarget selectedBoundary = childTarget
  /-- Equation (28): `P⁰U = U` on `E`. -/
  prescribed_harmonic :
    ∀ z ∈ Continuing, ∀ i : ι,
      U z i = expect (prescribedStep z) fun y => U y i
  /-- Equation (28): `P_i^aU_i ≤ U_i` on `E`. -/
  deviation_super :
    ∀ d : DevRow, devSource d ∈ Continuing →
      expect (devKernel d) (fun y => U y (devOwner d)) ≤
        U (devSource d) (devOwner d)
  /-- The unilateral bias potential `H_i`. -/
  bias : ι → Arena → ℝ
  /-- The multiplier `λ_i ≥ 0`. -/
  slope : ι → ℝ
  slope_nonneg : ∀ i : ι, 0 ≤ slope i
  /-- Equation (32): the finite dual form of the nonpositive
  neutral-occupation condition (31).  The right-hand side is `λ_i` times the
  nonnegative target slack (29). -/
  debt_dual :
    ∀ d : DevRow, devSource d ∈ Continuing →
      devCharge d +
          (expect (devKernel d) (bias (devOwner d)) -
            bias (devOwner d) (devSource d)) ≤
        slope (devOwner d) *
          (U (devSource d) (devOwner d) -
            expect (devKernel d) fun y => U y (devOwner d))
  /-- The prescribed bias potential `H_i^0`. -/
  prescribedBias : ι → Arena → ℝ
  /-- Equation (33): exact two-sided prescribed delivery. -/
  prescribed_debt :
    ∀ z ∈ Continuing, ∀ i : ι,
      prescribedCharge z i +
          (expect (prescribedStep z) (prescribedBias i) -
            prescribedBias i z) = 0
  /-- Stopping witness: the positive-support graph inside `E` is acyclic. -/
  exitRank : Arena → ℕ
  exitRank_prescribed :
    ∀ z ∈ Continuing, ∀ y : Arena, prescribedStep z y ≠ 0 →
      exitRank y < exitRank z
  exitRank_deviation :
    ∀ d : DevRow, devSource d ∈ Continuing →
      ∀ y : Arena, devKernel d y ≠ 0 →
        exitRank y < exitRank (devSource d)

namespace RobustFiniteEntry

variable {ι : Type} {parentTarget childTarget : ι → ℝ}

/-- Nonnegative target slack (29): `s_i(z, a) = U_i(z) − (P_i^aU_i)(z)`. -/
def slack (gate : RobustFiniteEntry ι parentTarget childTarget)
    (d : gate.DevRow) : ℝ :=
  gate.U (gate.devSource d) (gate.devOwner d) -
    expect (gate.devKernel d) fun y => gate.U y (gate.devOwner d)

theorem slack_nonneg (gate : RobustFiniteEntry ι parentTarget childTarget)
    (d : gate.DevRow) (hd : gate.devSource d ∈ gate.Continuing) :
    0 ≤ gate.slack d :=
  sub_nonneg.2 (gate.deviation_super d hd)

/-- **Falsifier probe for gate 3 / the answer's entry counterexample (39).**
A deviation self-loop inside the continuing region is impossible.  In the
answer's example `U ≡ 0` satisfies (28) while the deviator stays at `z`
forever; gate 3 rejects exactly that. -/
theorem no_deviation_selfLoop
    (gate : RobustFiniteEntry ι parentTarget childTarget) (d : gate.DevRow)
    (hd : gate.devSource d ∈ gate.Continuing)
    (hloop : gate.devKernel d (gate.devSource d) ≠ 0) : False :=
  Nat.lt_irrefl _ (gate.exitRank_deviation d hd _ hloop)

/-- No nonempty prescribed-closed set of continuing modes exists: prescribed
almost-sure stopping. -/
theorem no_closed_set_in_continuing
    (gate : RobustFiniteEntry ι parentTarget childTarget)
    (S : gate.Arena → Prop)
    (hsub : ∀ z, S z → z ∈ gate.Continuing)
    (hclosed : ∀ z, S z → ∀ y, gate.prescribedStep z y ≠ 0 → S y)
    (z : gate.Arena) (hz : S z) : False := by
  have key : ∀ n : ℕ, ∀ y : gate.Arena, gate.exitRank y = n → S y → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro y hy hSy
        obtain ⟨next, hnext⟩ := (gate.prescribedStep y).support_nonempty
        have hne : gate.prescribedStep y next ≠ 0 :=
          PMF.mem_support_iff _ _ |>.1 hnext
        have hlt := gate.exitRank_prescribed y (hsub y hSy) next hne
        exact ih (gate.exitRank next) (hy ▸ hlt) next rfl
          (hclosed y hSy next hne)
  exact key (gate.exitRank z) z rfl hz

/-- Finset form: there is no reachable closed `P⁰`-class inside `E`. -/
theorem no_closed_class_in_continuing
    (gate : RobustFiniteEntry ι parentTarget childTarget)
    (S : Finset gate.Arena) (hne : S.Nonempty)
    (hsub : ∀ z ∈ S, z ∈ gate.Continuing)
    (hclosed : IsPMFClosed gate.prescribedStep S) : False := by
  obtain ⟨z, hz⟩ := hne
  exact gate.no_closed_set_in_continuing (fun y => y ∈ S) hsub
    (fun y hy next hnext => hclosed hy hnext) z hz

/-- **The exact neutral-occupation condition (31), derived from the finite dual
(32).**  Every invariant occupation of owner `i` that is supported on
target-neutral continuing rows has nonpositive mean entry-debt charge. -/
theorem neutralOccupation_charge_nonpos
    (gate : RobustFiniteEntry ι parentTarget childTarget)
    [Finite gate.Arena] [DecidableEq gate.Arena] [Fintype gate.DevRow]
    (i : ι) (mass : gate.DevRow → ℝ)
    (mass_nonneg : ∀ d, 0 ≤ mass d)
    (owner : ∀ d, gate.devOwner d = i)
    (continuing : ∀ d, gate.devSource d ∈ gate.Continuing)
    (balanced :
      ∀ z : gate.Arena,
        ∑ d : gate.DevRow,
          mass d *
            actualOccupationColumn gate.devKernel gate.devSource d z = 0)
    (neutral : ∑ d : gate.DevRow, mass d * gate.slack d = 0) :
    ∑ d : gate.DevRow, mass d * gate.devCharge d ≤ 0 := by
  letI : Fintype gate.Arena := Fintype.ofFinite gate.Arena
  have drift_zero :
      ∑ d : gate.DevRow,
        mass d *
          (expect (gate.devKernel d) (gate.bias i) -
            gate.bias i (gate.devSource d)) = 0 := by
    have step : ∀ d : gate.DevRow,
        mass d *
            (expect (gate.devKernel d) (gate.bias i) -
              gate.bias i (gate.devSource d)) =
          ∑ z : gate.Arena,
            gate.bias i z *
              (mass d *
                actualOccupationColumn gate.devKernel gate.devSource d z) := by
      intro d
      rw [← potential_pair_actualOccupationColumn gate.devKernel
        gate.devSource (gate.bias i) d, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [Finset.sum_congr rfl fun d _ => step d, Finset.sum_comm]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [← Finset.mul_sum, balanced z, mul_zero]
  have key : ∀ d : gate.DevRow,
      mass d * gate.devCharge d ≤
        mass d *
          (gate.slope i * gate.slack d -
            (expect (gate.devKernel d) (gate.bias i) -
              gate.bias i (gate.devSource d))) := by
    intro d
    have h := gate.debt_dual d (continuing d)
    rw [owner d] at h
    have hslack : gate.slack d =
        gate.U (gate.devSource d) i -
          expect (gate.devKernel d) fun y => gate.U y i := by
      simp only [slack, owner d]
    refine mul_le_mul_of_nonneg_left ?_ (mass_nonneg d)
    rw [hslack]
    linarith
  calc
    ∑ d : gate.DevRow, mass d * gate.devCharge d ≤
        ∑ d : gate.DevRow,
          mass d *
            (gate.slope i * gate.slack d -
              (expect (gate.devKernel d) (gate.bias i) -
                gate.bias i (gate.devSource d))) :=
      Finset.sum_le_sum fun d _ => key d
    _ =
        gate.slope i * (∑ d : gate.DevRow, mass d * gate.slack d) -
          ∑ d : gate.DevRow,
            mass d *
              (expect (gate.devKernel d) (gate.bias i) -
                gate.bias i (gate.devSource d)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun d _ => by ring
    _ = 0 := by rw [neutral, drift_zero]; ring

end RobustFiniteEntry

/-! ## Gate 4: target-constrained germ coherence -/

/-- **Gate 4.**  The selected child target is the endpoint of a germ whose
strategic realization is the strategic restriction of the parent's.

This covers the inherited case (`childGerm = restrict parentGerm`, with
`restrict` folded into the choice of `childGerm`) and the restarted case with a
compatible interface morphism, i.e. the answer's (40)–(42).  The controlled
all-accuracy approximation (43) is **not** modelled.

The types are neutral parameters because the tree currently has no analytic
restriction map `R_C^an` on `AnalyticBellmanGerm`; instantiating `Interface` by
a subsingleton makes `commutes` vacuous, so faithfulness of this gate depends
entirely on the instantiation. -/
structure TargetConstrainedGermCoherence (ι : Type) (childTarget : ι → ℝ) :
    Type 1 where
  ParentGerm : Type
  ChildGerm : Type
  /-- The common strategic interface: public modes, realized kernels, target
  fields, rebasing maps and accounts. -/
  Interface : Type
  parentGerm : ParentGerm
  childGerm : ChildGerm
  /-- `ev₀`: endpoint evaluation. -/
  endpointOf : ChildGerm → (ι → ℝ)
  /-- `Φ_P`: analytic-to-strategic realization at the parent. -/
  parentRealization : ParentGerm → Interface
  /-- `Φ_C`: analytic-to-strategic realization at the child. -/
  childRealization : ChildGerm → Interface
  /-- `R_C^str`: the strategic restriction map. -/
  strategicRestriction : Interface → Interface
  /-- Equations (41)/(42): the germ's endpoint is the selected child target. -/
  endpoint : endpointOf childGerm = childTarget
  /-- Equation (40): the analytic and strategic restrictions commute. -/
  commutes :
    childRealization childGerm =
      strategicRestriction (parentRealization parentGerm)

/-- **Falsifier probe for gate 4 / the answer's Part D counterexample.**  Two
child germs may have the same endpoint vector and different strategic
interfaces.  The `endpoint` field alone therefore does not imply the
`commutes` field: a germ with the correct numerical endpoint can be unrelated
to the selected strategic child. -/
theorem germEndpoint_not_sufficient :
    ∃ (ChildGerm Interface : Type) (endpointOf : ChildGerm → (Unit → ℝ))
      (childRealization : ChildGerm → Interface) (target : Unit → ℝ)
      (left right : ChildGerm),
      endpointOf left = target ∧ endpointOf right = target ∧
        childRealization left ≠ childRealization right :=
  ⟨Bool, Bool, fun _ _ => 0, id, fun _ => 0, false, true,
    rfl, rfl, by simp⟩

/-! ## Gate 5: hereditary intrinsic progress -/

/-- **Gate 5.**  After minimal strategic closure and canonical bisimulation
quotient, *every* reachable descendant of the child has strictly smaller
canonical global rank than the parent — the answer's (47) with (50)/(51).

`self_descendant` records the answer's "the maximum includes `Γ` itself"; it is
load-bearing, see `hereditaryProgress_descends_vacuous_without_self`. -/
structure HereditaryIntrinsicProgress {Node Rank : Type}
    (rank : Node → Rank) (rankLt : Rank → Rank → Prop)
    (Descendant : Node → Node → Prop) (parent child : Node) : Prop where
  /-- The child is one of its own reachable descendants. -/
  self_descendant : Descendant child child
  /-- Hereditary strict global rank descent. -/
  descends : ∀ d : Node, Descendant child d → rankLt (rank d) (rank parent)

/-- **Falsifier probe for gate 5.**  Without `self_descendant`, the hereditary
descent field is satisfied by the empty descendant relation while the strict
descent at the child fails.  The reflexivity field is therefore not
decoration. -/
theorem hereditaryProgress_descends_vacuous_without_self :
    ∃ (rank : Unit → ℕ) (rankLt : ℕ → ℕ → Prop)
      (Descendant : Unit → Unit → Prop) (parent child : Unit),
      (∀ d : Unit, Descendant child d → rankLt (rank d) (rank parent)) ∧
        ¬rankLt (rank child) (rank parent) :=
  ⟨fun _ => 0, (· < ·), fun _ _ => False, (), (),
    fun _ h => h.elim, Nat.lt_irrefl 0⟩

/-! ## The bundle and the easy direction -/

section Bundle

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : StochasticGame ι)
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {Row : Type} [Fintype Row]

/-- The legal-entry interface used by the promotion output: gate 3 holds at the
node, delivering the selected child's whole target.

Defining the interface to *be* gate 3 avoids an unearned abstract hypothesis in
`PublicRecurrentClassChild`. -/
def LegalRobustEntry {Node : Type} (target : Node → ι → ℝ)
    (childTarget : ι → ℝ) (node : Node) : Prop :=
  Nonempty (RobustFiniteEntry ι (target node) childTarget)

/-- **The five-gate witness** for one candidate analytic class `C`, one
realization cell, and one legal target/rebasing cell.

`child_entry` and `child_target` identify the abstract node `child` with the
child datum produced by gates 1–2; they are *not* the conclusion.  The
conclusion `target child = target parent` is derived. -/
structure FiveGateData
    (rowOwner : Row → ι) (rowSource : Row → G.State)
    (rowKernel : Row → PMF G.State) (rowPayoff : Row → ι → ℝ)
    (prescribedKernel : G.State → PMF G.State)
    (prescribedPayoff : G.State → ι → ℝ)
    (classRows : Finset Row)
    (CellFiber : (G.State → ι → ℝ) → Prop)
    {Node Rank : Type}
    (entry : Node → G.State) (target : Node → ι → ℝ)
    (rank : Node → Rank) (rankLt : Rank → Rank → Prop)
    (Descendant : Node → Node → Prop) (parent child : Node) : Type 1 where
  /-- Gate 1: common support realization. -/
  gate1 :
    CommonSupportRealization G rowOwner rowSource rowKernel prescribedKernel
      classRows (entry parent)
  /-- Gate 2: complete target compatibility, in the same class. -/
  gate2 :
    CompleteTargetCompatibility G rowOwner rowSource rowKernel rowPayoff
      prescribedKernel prescribedPayoff classRows gate1.core.states CellFiber
      (target parent) gate1.core.entry
  /-- The abstract child node is the child produced by gates 1–2. -/
  child_entry : entry child = gate2.childEntry
  /-- Its declared target is the gate-2 child target. -/
  child_target : target child = gate2.childTarget
  /-- Gate 3: robust finite entry synthesis delivering that target. -/
  gate3 : RobustFiniteEntry ι (target parent) gate2.childTarget
  /-- Gate 4: target-constrained germ coherence at that target. -/
  gate4 : TargetConstrainedGermCoherence ι gate2.childTarget
  /-- Gate 5: hereditary intrinsic progress. -/
  gate5 : HereditaryIntrinsicProgress rank rankLt Descendant parent child

/-- The exact output tuple (4) of the promotion theorem, together with the
canonical child `Q` it names. -/
structure PromotionOutput
    (rowOwner : Row → ι) (rowSource : Row → G.State)
    (rowKernel : Row → PMF G.State)
    (prescribedKernel : G.State → PMF G.State)
    {Node Rank : Type}
    (entry : Node → G.State) (target : Node → ι → ℝ)
    (rank : Node → Rank) (rankLt : Rank → Rank → Prop)
    (parent child : Node) : Type 1 where
  /-- Component 1: common behavior. -/
  commonBehavior :
    CommonProfileRowRealization G rowOwner rowSource rowKernel prescribedKernel
  /-- Component 2: the child's whole target `w_C` … -/
  wholeTarget : ι → ℝ
  child_target : target child = wholeTarget
  /-- … preserved as a complete payoff vector. -/
  target_preserved : target child = target parent
  /-- Component 3: robust entry. -/
  robustEntry : RobustFiniteEntry ι (target parent) wholeTarget
  /-- Component 4: germ coherence. -/
  germCoherence : TargetConstrainedGermCoherence ι wholeTarget
  /-- Component 5: strict intrinsic progress. -/
  strictProgress : rankLt (rank child) (rank parent)
  /-- The canonical child `Q`. -/
  recurrentChild :
    PublicRecurrentClassChild prescribedKernel entry target rank rankLt
      (LegalRobustEntry target wholeTarget) parent
  recurrentChild_child : recurrentChild.child = child

namespace FiveGateData

variable {G}
  {rowOwner : Row → ι} {rowSource : Row → G.State}
  {rowKernel : Row → PMF G.State} {rowPayoff : Row → ι → ℝ}
  {prescribedKernel : G.State → PMF G.State}
  {prescribedPayoff : G.State → ι → ℝ}
  {classRows : Finset Row}
  {CellFiber : (G.State → ι → ℝ) → Prop}
  {Node Rank : Type}
  {entry : Node → G.State} {target : Node → ι → ℝ}
  {rank : Node → Rank} {rankLt : Rank → Rank → Prop}
  {Descendant : Node → Node → Prop} {parent child : Node}

/-- **Easy direction, core step.**  The five gates produce the canonical
recurrent child: a legal reachable closed class of the realized public kernel,
carrying the parent's *whole* payoff-vector target, at strictly smaller rank.

Whole-target preservation is not assumed anywhere: it is transported from
gate 2's harmonicity by `ReachableClosedClass.harmonicVector_eq_entry` inside
`PublicRecurrentClassChild.of_harmonicClassTarget`.  Strict descent is gate 5
instantiated at the child. -/
def promote
    (data :
      FiveGateData G rowOwner rowSource rowKernel rowPayoff prescribedKernel
        prescribedPayoff classRows CellFiber entry target rank rankLt
        Descendant parent child) :
    PublicRecurrentClassChild prescribedKernel entry target rank rankLt
      (LegalRobustEntry target data.gate2.childTarget) parent :=
  PublicRecurrentClassChild.of_harmonicClassTarget data.gate1.core
    data.gate2.targetField data.gate2.prescribed_harmonic
    data.gate2.parent_balance child data.gate2.childEntry
    data.gate2.childEntry_mem data.child_entry
    (data.child_target.trans data.gate2.child_target_eq)
    (data.gate5.descends child data.gate5.self_descendant)
    ⟨data.gate3⟩

omit [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- The promoted child's whole payoff vector equals the parent's. -/
theorem childTarget_eq_parentTarget
    (data :
      FiveGateData G rowOwner rowSource rowKernel rowPayoff prescribedKernel
        prescribedPayoff classRows CellFiber entry target rank rankLt
        Descendant parent child) :
    data.gate2.childTarget = target parent :=
  data.child_target.symm.trans data.promote.target_preserved

/-- **Easy direction, full output.**  The five gates assemble into the exact
output tuple (4): common behavior, whole target, robust entry, germ coherence,
strict intrinsic progress — together with the canonical child. -/
def output
    (data :
      FiveGateData G rowOwner rowSource rowKernel rowPayoff prescribedKernel
        prescribedPayoff classRows CellFiber entry target rank rankLt
        Descendant parent child) :
    PromotionOutput G rowOwner rowSource rowKernel prescribedKernel entry
      target rank rankLt parent child where
  commonBehavior := data.gate1.toCommonProfileRowRealization
  wholeTarget := data.gate2.childTarget
  child_target := data.child_target
  target_preserved := data.promote.target_preserved
  robustEntry := data.gate3
  germCoherence := data.gate4
  strictProgress := data.gate5.descends child data.gate5.self_descendant
  recurrentChild := data.promote
  recurrentChild_child := rfl

omit [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- **Easy direction, propositional form.**  All five gates hold ⇒ the
promotion holds. -/
theorem exists_promotionOutput
    (data :
      FiveGateData G rowOwner rowSource rowKernel rowPayoff prescribedKernel
        prescribedPayoff classRows CellFiber entry target rank rankLt
        Descendant parent child) :
    Nonempty
      (PromotionOutput G rowOwner rowSource rowKernel prescribedKernel entry
        target rank rankLt parent child) :=
  ⟨data.output⟩

end FiveGateData

end Bundle

end ProperSupportGatePromotion
end StochasticGame
end GameTheory

