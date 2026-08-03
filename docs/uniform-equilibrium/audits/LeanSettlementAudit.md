# Lean Settlement Audit after the Sorin target correction (v3)

> **Scope note (2026-08-01):** this file is the detailed historical audit,
> dependency ledger, and interface-safety record. The operational program is
> now split into `MathResearchMethod.md`, `LeanFormalizationMethod.md`, and
> `ParallelResearchMethod.md`, coordinated by
> `UniformEquilibriumProgram.md`. The mutable theorem boundary and working
> hypotheses are in `UniformEquilibriumCurrentFrontier.md`. Mathematical
> discovery and Lean execution should no longer be scheduled as one
> undifferentiated plan.
>
> **Scheduling note (2026-08-02):** the operative queue is maintained in the
> "Operative queue" section of `UniformEquilibriumCurrentFrontier.md`. The
> step list below is kept for its dependency analysis; per-item status was
> reconciled against the committed tree on 2026-08-02 (commit hashes cited
> inline). Do not schedule from this file without checking those statuses.
>
> **Credibility update (2026-08-02, after Q94--Q99):** Q95 supplies the
> fixed-public gain--bias verifier and corrects Q53's target-level
> counterexample. Its corrected (F1)/(C2) arithmetic and sufficiency direction
> have been independently checked; the answer as a whole does not yet carry an
> adversarial verification seal. Q96 has now checked the reachable multichain
> converse and both cap quantifier orders, while refuting the unconditional
> four-condition occupation equivalence: exactness requires recurrent coverage
> (RC) or a fifth uncovered-positive-surplus obstruction. Q97 has now
> independently checked the quitting-game (Q1)--(Q5) characterization and
> proved FTV three-phase minimality/rigidity; its weighted-regret counterfamily
> fences approximate interfaces. Q98 gives a source-conditional proof that the
> unbounded finite-public language is recursively enumerable complete, so no
> total computable node bound exists, while each fixed bound remains decidable;
> its external finite-state-SPE premise is stated by its primary source with a
> proof sketch, and its bridge is internal. Q99 concerns only verification of
> one supplied rational homogeneous private controller under a product belief
> filter; synthesis and strategy-class completeness are excluded. The known
> finite-POMDP theorem supplies existence of its unrestricted asymptotic value
> and deterministic finite-memory approximation. An audited, timing-exact PFA
> embedding now makes the threshold hierarchy sharp in Q99's own class:
> \(L>c\) is \(\Sigma^0_1\)-complete, \(L\le c\) is
> \(\Pi^0_1\)-complete, \(L\ge c\) and \(L=c\) are
> \(\Pi^0_2\)-complete, and \(L<c\) is \(\Sigma^0_2\)-complete. Strict
> violations have finite transducer witnesses,
> but cap acceptance has no complete recursively enumerable finite
> rational/algebraic certificate family. The reduction is internal and not
> Lean-formalized. Q99's appended answer additionally claims a repaired
> historywise \(\Pi^0_1\) classification and an effective-clock
> \(\Pi^0_3\) classification. Those claims are answer-received but await the
> focused adversarial passes in `ephemeral/reviews/Review01-*` and
> `Review02-*`; the automatic-clock exact boundary remains open. Exact
> attainment, the requested stationary distinctions, tight complexity, useful
> decidable subclasses, and the restricted \(\eta\)-optimal memory-bound
> question are still unsettled or omitted. Q94 proves
> that the public class is not a universal strategy representation and leaves
> clocked-private completeness open. The global and support-pruned Q56
> criterion directions are build-checked, umbrella-imported, and committed at
> `24b5bf7`. The split-domain arbitrary-start telescopes and explicit-domain
> verifier are landed at `cbf1ab4` and `83b1826`. The actual FTV ten-node
> adapter is also formalized and landed at
> `8090347`, and the two cap-definition regression separators are landed at
> `97178e6`. Q96's two-player/two-node escaped prescribed-class regression is
> landed at `68149dd`: it machine-checks the four passing tests, the uncovered
> positive recurrent surplus, linear delivery failure, and Poisson
> impossibility. The later semantic-converse chain now culminates in
> `SplitDomainNeutralOccupationConverse.lean` (`4f12352`): shifted delivery and
> all-behavior caps produce both split-domain gain--bias families and imply
> owner-local `(N)`. The exact all-start semantic iff wrapper is now landed at
> `fcf3ff4`. It characterizes the supplied split architecture and does not
> assert `(RC)`, architecture synthesis, or unrestricted coverage. The
> corrected `(RC)`/fifth-obstruction exhaustion,
> rational rejection packets, both horizon-order identities, and sharp span
> constants remain unformalized. Q97's exact cyclic packet minimum and
> normalized three-phase rigidity are landed in `FTVCyclicMinimality.lean`
> (`408bf3b`); its equilibrium-theoretic `(Q1)--(Q5)` bridge, sharp modulus,
> and weighted-regret boundary remain outside Lean.
>
> **Sorin separation status (2026-08-02):** the tracked base-game package and
> the separation law were different deliverables; both are now landed. Review
> 05 reconstructed the primary-source proof, and the subsequent Lean chain
> formalizes both security adapters, deterministic cone resets, live-tail
> accounting, the target-free `14ε` survival/occupation bound, and the
> unconditional exclusion of `(1/2,2/3)`. The capstone is
> `SorinOccupationVanishing.lean` (`c1161dc`), importing the separation
> interface landed at `6b0fc81`. This closes the endpoint-separation fence, not
> the converse realization of every point on Sorin's uniform segment.
>
> **Correlation and leaf-gate update (2026-08-02):** Review 04 verifies Q100's
> witnesswise private-recommendation separator and corrects the source reading:
> Solan--Vieille's punishment is an ordinary coalition minmax that ignores the
> continuing device signals. The scalar sharp product-law gap is landed at
> `a6a66b5`, and its pure-action payoff-preserving four-state absorbing lift at
> `9f8aece`. The arbitrary mixed-root law/update bridge is landed at
> `afe018c`, and `a9cb4ca` excludes exactly the mediated target `(5/7,5/7)`
> as a uniform-equilibrium payoff of the lift. This is not target-free
> nonexistence, retargeting exhaustion, an autonomous device, or a universal
> compiler/noncompiler theorem. `DeclaredTargetLeafGates.lean` (`69006ce`) now
> lands the neutral declared-target wrapper and finite gluing/bridge/custody
> gates. `EndpointHarmonicTriviality.lean` (`ab3d671`) proves that the endpoint
> transition algebra restricted to the harmonic submodule yields no richer
> rank than ordinary dimension. Canonical genuine Bellman-row extraction is
> now landed at `43d410b`; transition-monitoring identification and credible
> public-response realization remain open and distinct. Commit `1f097d2`
> umbrella-imports the global nonexistence interface and corrects the
> fixed-depth/variable-stopping roadmap. The single-controller no-trap kernel
> is landed at `914c765` and its rank-decreasing policy compiler at
> `d9f212e`. The fixed-kernel reachability-to-zero-occupation/transience step
> and mean-ergodic projection inequality remain open.

Revised 2026-07-31, twice: first by the wave review, then corrected after
external review (gate-or-alternative framing, dependency-ordered execution,
build-verified module status, restored Q55--69 ledger). Companion documents:
[WaveReviewQ70-78.md](../../../ephemeral/old/WaveReviewQ70-78.md) (review + erratum),
[Question79-InertMixedCertificateDirectClosure.md](../../../questions/old/Question79-InertMixedCertificateDirectClosure.md),
[Question80-AdaptiveSemanticLeafSupply.md](../../../questions/old/Question80-AdaptiveSemanticLeafSupply.md).
Revised again on 2026-08-01 after
the Sorin endpoint-target no-go and the research audit in
`ResearchSynthesis.md`.

## Critical correction: the germ endpoint is not the root target

Sorin's two-player absorbing game has a rational analytic stationary
discounted Nash germ with the constant payoff endpoint
\((1/2,2/3)\), while every uniform-equilibrium payoff is of the form
\((\alpha,2(1-\alpha))\), \(1/2\le\alpha\le2/3\). Hence the endpoint is
not a uniform-equilibrium payoff. The calculation and primary citation are in
`UniformEquilibriumFrontierManuscript.tex`.

This invalidates any universal Lean interface of the form

~~~text
analytic germ/leaf at endpoint v
  -> adaptive certificate at the same v.
~~~

The correct type-level architecture is

~~~text
discounted-equilibrium correspondence
  -> endogenous GermTargetSelectionOutput carrying a chosen germ and some implementable w
  -> local resolution and recursive children with explicit target bridges
  -> a sound certificate at w or the semantic deviation-cap constructor.
~~~

Root retargeting and internal target preservation are different. The root may
replace the discounted endpoint. Once `w` is declared, every child, splice,
and rebasing theorem must preserve the complete vector or carry an explicit
proved bridge to a newly declared child target. Existing target-transport
lemmas remain useful under this interpretation. Any existing reconstruction
socket definitionally fixed to `germ.endpointValue` is overstrong and must not
be used as the intended universal settlement interface.

The germ itself is existential data. A settlement theorem may choose a
favorable analytic branch; it need not close every arbitrary germ. Therefore
the root output must record both branch selection and target selection.
Closing all thirteen leaf types remains a sufficient conservative program,
but a checked arc-selection theorem may legitimately eliminate leaf classes.
Sorin shows that branch selection alone is insufficient: the chosen uniform
target may still have to differ from every discounted endpoint.

## Second critical correction: Question 84's absolute remainder is too strong

Question 84 has a negative answer. In an action-independent three-state game,
the initial state moves with equal probability to absorbing rewards (+1)
and (-1). The unique ex-ante target is (0), and a trivial uniform
equilibrium exists, but the proposed combination of historywise local drift
and

\[
\mathbb E[C_N+|\Phi_N-\Phi_0|]=o(N)
\]

is impossible. The two public branches cancel in expected payoff, while the
absolute terminal bound destroys the cancellation.

This does not refute `IsAdaptivePotentialCertificateAt`, whose verifier uses
expectation-level monotonicity rather than Question 84's absolute remainder.
It means that Question 84 is an interface-falsification result, not the
capstone. The existing adaptive certificate remains a sound route, but no
single certificate syntax is to be treated as universally complete without a
proof. The semantic waist remains `HasUniformDeviationCapConstructor`, which
is exactly equivalent to a uniform-equilibrium payoff.

## Current status

Questions 19--85 have answers. Question 84 is a negative certificate-boundary
result. Question 85 supplies the coupled-scale Abel reduction, exact
finite-mode occupation--flux criteria, and a nonclosed deterministic
attainment boundary. The
routing wave (Q70--75), plateau
(Q76), audit (Q77), and compiler (Q78) share one disciplined shape: sound
finite theorems, a named missing invariant, and a finite counterexample
showing the invariant is not free.

The later credibility and representation questions now have a sharp but
stratified status. Q93's literal (S4)--(S5) certificate class is too strong for
FTV; Q95's configuration-dependent target field is the adopted repair. The
Q95 sufficiency direction answers supplied-architecture verification. Q96 now
proves its gain--bias converse and finite obstruction statement after exposing
the missing cross-owner recurrent-class case. The four-condition occupation
form is exact only under (RC); otherwise the fifth obstruction is mandatory.
Q97 now seals the quitting-game characterization on its stated uniformly
absorbing cyclic class, proves the FTV minimum and rigidity, and refutes
probability-weighted local regret as an approximate strategic criterion. Q98
proves, conditional on its sourced finite-state-SPE premise, that the unbounded
public-node union is recursively enumerable complete:
there is no total computable per-input node bound or universal finite-public
producer, even though fixed-node synthesis is decidable. Its terminal bridge
is reachable-history exact and uses graph trimming before all-node completion.
Q94 answers with the current literature boundary rather
than resolving its A/B dichotomy: finite-public completeness is false, while
clocked-private completeness is open already in zero-sum games. These results
must not be compressed into either “credibility remains wholly open” or
“credible architectures are now complete.”

The named invariants, question by question:

| Q | Invariant / gate |
|---:|---|
| 70 | public-resampling hypothesis (for any mode bound); no dimension-only bound exists |
| 71 | mixed-owner gluing / zero global holonomy |
| 72 | owner-complete routing exactness (custody of every target coordinate) |
| 73 | route-complete restriction R1--R4 (preserve the first nonzero analytic jet) |
| 74 | strategic account-completeness (observability + bipolar orientation + bridge duality + shift compactness) |
| 75 | target-constrained leaf lifting + route completeness |
| 76 | finite complete semantic signature; plateau SCCs closed as outputs, never traversed |
| 77 | decidable/proof-carrying certificate language; guarded routing registry with proved coverage |
| 78 | occurrence-level interfaces; pre-horizon accuracy selection |

**These are route gates, not invariants every leaf must supply.** Q71's
counterexample carries an explicit analytic germ that provably fails zero
holonomy, so the desired source theorem can never be "analytic leaf ⟹
named invariant." It must be the gate-or-alternative form:

~~~text
analytic leaf
  -> route invariant holds (gate passes)
  ∨ direct closure                       (Q79 / Route 0)
  ∨ semantic closure                     (Q80 / adaptive leaf)
  ∨ a typed obstruction with a proved consumer
~~~

A failed gate with no consumed alternative is an open vertex, full stop.

The residual mathematics falls into **five currently identified frontier
layers**:

- **Layer T** — endogenous germ and root-target selection. Analytic germs and
  endpoint leaves constrain and inform the target, but neither an arbitrary
  germ nor its endpoint is forced. A successful
  output must carry concrete finite-tree, stopping, occupation, or semantic
  data witnessing why the selected target can enter the post-selection
  resolver. Sorin's game is the mandatory falsification test.
- **Layer A** — gate-or-alternative theorems for actual analytic-germ
  leaves, through finite **or proof-carrying** typed interfaces. Q71
  holonomy and Q72 custody are finite; Q73 needs proof-carrying analytic
  data (equality of arbitrary real-analytic germs is not decidable); Q74
  shift compactness is asymptotic; Q75 includes strategic realization.
- **Layer B** — Route 0 (Q79): direct closure for strategically inert
  mixed certificates. The two-state acceptance instance is bounded; the
  general upgrade from stationary harmlessness to shifted finite-horizon
  deviation caps may itself be conjecture-level.
- **Layer C** — adaptive semantic leaves (Q80). Q80 bundles four distinct
  projects (classification, interface, known-class supply, self-similarity)
  and must be split before broader Lean implementation; Part E can contain the
  original conjecture. The exact two-stage zero-target-debt Big-Match loop from
  Part D is landed at `61106b1`, but the arbitrary-controller routing theorem
  and any rank consequence remain open.
- **Layer R** — response-architecture production and representation. For a
  supplied finite public Markov architecture, Q56/Q95 give the checked sound
  direction of the credibility verifier; Q95 proposes the exact converse. The
  Lean tree now checks both the sound direction and the split-domain semantic
  necessity spine: shifted delivery and all-behavior caps yield prescribed and
  unilateral biases and owner-local neutral-occupation nonpositivity.
  Q96 corrects the finite obstruction packet with `(RC)` or a fifth
  cross-owner recurrent witness; that packet's exhaustion and rational
  rejection theorem remain to be formalized. Q98 settles the separate
  computable public-node-bound problem negatively. What remains is to
  formalize the corrected rejection alternative, build structured producers where possible despite Q98's
  undecidability boundary, and keep this public class separate from Q94's open
  clocked-private completeness problem. Q99 is a mathematical verification
  question with precise supplied-controller semantics. Its external
  finite-POMDP baseline and internal PFA embedding now determine the numeric
  value identity, the exact arithmetic threshold hierarchy, finite rejection
  certificates, and the impossibility of a complete enumerable finite cap-
  acceptance certificate family. None is yet a Lean theorem or API
  specification. The open Q99 work is exact attainment, stationary and
  fixed-memory subclasses, a restricted-class computable
  \(\eta\)-optimal-memory bound, useful decidable subclasses, and the stronger
  historywise/reset and clocked variants.

Layers A--C are now understood as operating relative to a declared selected
target. They cannot restore an analytically forbidden endpoint by better
accounting.

Q76→Q77→Q78 form a conditional chain; no link counts as progress until its
hypotheses are discharged (conditional theorems stay amber, zero closure
credit).

## Two ledgers

Track separately, and never let one masquerade as the other:

1. **Formalization progress** — interfaces, counterexamples, registries,
   compilers landed sorry-free and axiom-clean.
2. **Closure progress** — analytic leaf classes unconditionally consumed.

Current closure credit from the entire Q70--78 wave: **zero**. The
unconditional chain today ends at the typed endpoint leaf
(`exists_initialAnalyticEndpointLeaf`).

## Current synthesis questions and consequences

| Number | File | Role |
|---:|---|---|
| 79 | [Question79-InertMixedCertificateDirectClosure.md](../../../questions/old/Question79-InertMixedCertificateDirectClosure.md) | Route 0 and restored five-route exhaustivity, or the next counterexample |
| 80 | [Question80-AdaptiveSemanticLeafSupply.md](../../../questions/old/Question80-AdaptiveSemanticLeafSupply.md) | Routing-resistant classification; semantic interface; class supply; self-similarity (split before formalizing) |
| 81 | [Question81-AdaptiveAbelCesaroRealization.md](../../../questions/old/Question81-AdaptiveAbelCesaroRealization.md) | Negative answer: open-loop analytic calendars do not generally deliver even a feasible Markov endpoint |
| 82 | [Question82-FeedbackAbelCesaroRealization.md](../../../questions/old/Question82-FeedbackAbelCesaroRealization.md) | Answered one-scale feedback realization boundary and occupation/flux characterization |
| 83 | [Question83-ControlledAbelCesaroUniformCap.md](../../../questions/old/Question83-ControlledAbelCesaroUniformCap.md) | Open controlled delivery plus deviation cap |
| 84 | [Question84-EndogenousUniformTargetSelection.md](../../../questions/old/Question84-EndogenousUniformTargetSelection.md) | Negative: absolute terminal sublinearity destroys legitimate public-branch cancellation; signed expectation is enough for the elementary implication |
| 85 | [Question85-CoupledScaleAbelReduction.md](../../../questions/old/Question85-CoupledScaleAbelReduction.md) | Answered: canonical finite multiscale Abel hierarchy; exact randomized finite-mode occupation--flux criterion; deterministic exact attainment is nonclosed |

These are not the only remaining obligations: every Layer-A gate theorem
is unproved for actual leaves, and the Q55--69 translation ledger below is
open. Re-review flags (recorded as self-contained follow-up questions in
the files) gate the rank formalization: Q76 invariance (first), the Q60
coherence proviso, the Q68 strengthened reading.

## Q55--69 formalization ledger (audited 2026-07-31 night)

The previous plan's obligation to formalize the answered finite theorems
did not disappear because later questions were answered. The guess-table
has been replaced by a VERIFIED per-row audit against the answers' final
theorems and the actual Lean tree — full row notes with declarations in
`Q55-69LedgerAudit.md`. Summary (lean / adapter / consumer seals):

| # | Content | L | A | C | Top missing piece |
|---|---|---|---|---|---|
| Q55 | typed whole-target alternative | ~ | ~ | ✗ | owner-defect certificate branch as third disjunct |
| Q56a | fixed-public criterion direction | ✓ | ✓ | ✓ | landed criterion (`24b5bf7`) and actual FTV adapter (`8090347`); retain Q97 sharpness/minimality as a separate obligation |
| Q56/Q95/Q96 | fixed-class semantic iff and obstruction | ✓ | ✓ | ✓ | all-start semantic iff landed through `fcf3ff4`; formalize explicit `(RC)` or exhaustive fifth recurrent-class rejection packet separately |
| Q57 | calendar/ledger conversion | ✓ | ✓ | ✓ | block counterexample: prefix-sublinear ⇏ shift-uniform |
| Q58 | owner-history quotient | ~ | ~ | ~ | ker U ⊆ ker B ⟺ factorization, over the coboundary quotient |
| Q59/60 | canonical nodes + rank | ~ | ✓ | ~ | srank := finrank(D ⊓ ker L) + basis independence |
| Q61 | selector occupation duality | ~ | ✓ | ✓ | Thm 1 as an iff (bias ⟺ occupation + delivery) |
| Q62 | all-accuracy composition | ~ | ✓ | ~ | stopped-tree Nash transfer (discharges ObstacleCloseness) |
| Q63 | semantic stopping | ~ | ~ | ~ | spliced dispatcher ⇒ IsUEP with explicit 2ML/N |
| Q64 | attainable correspondence | ✗ | ✗ | ~ | define A_re + prove analytic-source/declared-target bridge; endpoint equality is only a special case |
| Q65-69 | gates / zero-pairing | ~ | ✓ | ~ | bundle the five gates; prove gates ⇒ promotion |

`✓*` means the declaration and umbrella build have been checked in the current
worktree, but the file is still untracked and therefore not yet landed in the
repository history. The `A` seal for Q56a remains absent until the actual FTV
architecture, rather than a toy probe, is compiled through the criterion.

Corrections the audit made to earlier guesses: Q55's alternative is already
whole-vector (not child-only); Q57's shifted-history labelling IS
systematic (`shiftedUniversalEpochScale`, `IsShiftedUniversalCalendar
ChargeAccountAt`) and Q57 is the strongest row; Q65 gate 1 (common support
realization) is substantially proved and bankable. Confirmed deepest
absence: Q64 — its correspondence appears in the tree only as the
`ChildObligations` hypothesis bundle, i.e. the theorem restated as an
assumption. After the Sorin correction, the universal obligation cannot be
“child germ endpoint equals declared target”; it must instead provide analytic
source data plus a genuine target bridge or a new endogenous child target.

## No-sorry Lean work, dependency-ordered

### 0. Stabilize the terminology rename

The `GateG` → `AnalyticBellmanGermExistence` rename (19 tracked files,
build-verified) is committed as an isolated change; the working-tree diff
was verified to contain nothing but the rename before committing.

### 1. Untracked modules — DONE (all repaired, verified, landed 2026-07-31 night)

All five formerly-untracked modules now compile, are imported by the
umbrella, and are committed (d64563d, c879fdc): the first-hit stopping
pair (dependent-match repair at :479), the profile-law transfer, the
finite-time target bounds (two linarith repairs), and the ranked
terminal-child closure prototype (whitespace-split identifier + three
defeq rw repairs; docstring honestly re-scoped to "partial prototype:
common terminal depth, `ObstacleCloseness` assumed"). Standing rule
retained: zero `sorry` does NOT mean compiling — nothing may be called
finished until its focused `lake build` passes.

### 2. Raw counterexample formalization (games and elementary facts only)

- **DONE (`c1161dc`, `6b0fc81`).** Sorin's base game, exact weighted
  finite-horizon accounting identity, both one-sided security adapters,
  deterministic cone resets, survival/tail accounting, `14ε`
  occupation-vanishing theorem, uniform-payoff hyperplane, and unconditional
  endpoint exclusion are tracked and umbrella-imported. This is the separation
  direction only; the converse construction of all points of Sorin's segment
  and generic extraction of the cone-reset machinery remain separate work.
- **DONE (b3fd1bb, 15d49dc).** Q71's two-state pure-externality game: game,
  exact deviation invariance, every-profile-is-an-equilibrium, direct
  `IsUniformEquilibriumPayoff` at (0,0) and (1,1)
  (`PureExternalityCycle.lean`), and the machine-checked Route-0 acceptance
  pair `routeZero_acceptance` (`PureExternalityCycleHolonomy.lean`).
  Remaining honest gap: no germ-level Bellman tagging of the example.
- **Covered at the abstract level (d9b741b).** Q77's self-child discipline
  keeper landed as the rule-system falsifier
  (`not_strictProgress_selfChildSystem` in `GuardedRoutingAudit.lean`); a
  game-level one-state version is optional.
- **Q72 falsifier DONE (fcfd1dc)** as `CrossOwnerCancellation` in
  `Math/LinearAlgebra/OwnerTypedDualLifting.lean`; Q75 example games remain
  open, as capacity allows.

Route-failure and audit-failure theorems against the *finite interface
cores* are landed (see steps 3–4). The leaf-level versions cannot precede
the leaf-facing interfaces of step 3.

### 3. Post-selection Layer-A interfaces only — defer the root selector

The six `*ReconstructionAt` records are consumed by the atlas eliminator and
the terminal-deflation route; do not restructure them in place. The
`GermTargetSelectionOutput` fields are not mathematically settled and must not
be frozen yet. For low-risk work, make only the post-selection target explicit
and build parallel local types:

~~~text
chosen leaf data + an explicitly declared target
  -> structured gate/obstruction data
  -> concrete LocalResolutionOutput at the declared target
  -> existing reconstruction boundary   (via proved consumers only)
~~~

- a neutral `DeclaredTargetNode` parameter which does not identify the target
  with `germ.endpointValue` and contains no implementability claim — **LANDED**
  in `DeclaredTargetLeafGates.lean` (`69006ce`), together with finite
  gluing/account-bridge/custody adapters and acceptance/failure probes. Its
  `NodeFlowRows.grossGain` is still supplied data: canonical extraction from
  actual analytic Bellman deviation rows is open;
- `MixedOwnerGluingData` (Q71: cochain, incidence, holonomy class) — finite
  core **landed** as `Math/LinearAlgebra/OwnerLabeledFlowHolonomy.lean`
  (fbacffe: `zeroHolonomy_iff_exists_accountPotential`, `TwoCycle`
  falsifier); the leaf-data record wrapping it is open
- `OwnerCustodyData` (Q72) — finite core **landed** as
  `Math/LinearAlgebra/OwnerTypedDualLifting.lean` (fcfd1dc:
  `hasTypedLift_iff_validOnVisible`, custody,
  `not_hasTypedLift_of_visibleRecession`); leaf-data record open
- `JetPreservingRestrictionData` (Q73; proof-carrying analytic fields) —
  **OPEN**, hardest of the five (germ equality is not decidable)
- `StrategicAccountCompletenessData` (Q74) — bridge/orientation core
  **landed** as `Math/LinearAlgebra/OrientedAccountBridge.lean` (424c7ec:
  `IsExactBridge`, `HasFullSupportCirculation` necessity, `ParallelRows` and
  `SelfLoop` falsifiers); observability and shift-compactness components and
  the leaf-data record open
- `TargetConstrainedRouteData` (Q75) — **OPEN**
- plateau/rank gate data (Q76 — the sixth socket needs treatment too) —
  **OPEN**, gated on the Q76 re-review; facial rank is refuted by Q91 and the
  endpoint-transition module filtration is formally trivial (`ab3d671`). The
  guarded-registry skeleton is landed as `GuardedRoutingAudit.lean` (d9b741b)
- a common `LocalResolutionOutput` carrying its declared target and, for every
  strict child, an explicit complete-vector target bridge (semantic / terminal
  / discharged / strict children / typed obstruction)

None of these contains an adaptive certificate. Only a proved consumer
converts a closed output into an existing reconstruction socket. Probe
every new Prop for vacuity with the zero/trivial witness.

The eventual root `GermTargetSelectionOutput` must additionally prove that
its chosen germ and target feed one of these post-selection consumers. It may
not contain an adaptive certificate, assume a uniform payoff, or assume a free
public correlation device. If it uses a public lottery, the strategy which
synthesizes and protects that lottery is part of the witness.

### 4. Route-failure theorems against the step-3 interfaces

**Landed at the finite-core level:** the Q71 `TwoCycle` holonomy falsifier
(fbacffe), the Q72 `CrossOwnerCancellation` falsifier (fcfd1dc), the Q74
`ParallelRows`/`SelfLoop` falsifiers (424c7ec), the Q77 self-child keeper
(d9b741b), and the machine-checked Route-0 acceptance pair (15d49dc).
**Open:** the Q71 four-route no-go stated against actual leaf-facing
predicates — this requires the step-3 leaf-data records first. Falsifier
discipline stands: every new interface Prop must survive the zoo.

### 5. Translate the conditional finite theorems (Q55--75 ledger)

Work the restored ledger against the step-3 types, with the acceptance
criteria below; every translated theorem keeps its architecture, complete
child library, and shifted-history premises.

Q56's criterion implication and the actual FTV ten-node adapter have now been
translated and landed separately at the finite public-architecture level. Do
not schedule duplicates of either result. Q96's semantic gain--bias converse
and exact all-start iff wrapper are landed on the exact split domains through
`fcf3ff4`, including Markov-deviation realization and owner-local `(N)`. What
remains is the corrected obstruction
extractor: either assume recurrent coverage `(RC)` before exposing the four
`(T0)/(Ti)/(N)/(P)` conditions as exact, or include and prove exhaustive the
fifth uncovered-positive-surplus recurrent-class packet. Q97's FTV
minimum/normalized-rigidity corollary is landed at `408bf3b`, but only from the
table-expanded cyclic packet. Any formal consumer of `(Q1)--(Q5)` as an exact
quitting-game equilibrium characterization must still formalize that semantic
bridge and preserve its uniformly absorbing cyclic domain.

The credibility regression suite must test not only Q53, the
neutral-occupation falsifier, Big Match, and FTV, but also both Q95 `6 cap
separators: the one-state \((A,L)\) example separating architecture cap from
minmax, and the `Stay`/`Go`/`Back`/`Exploit` example separating a complete
unilateral strategy from one action followed by obedience.

### 6. Formalize Q79, then split Q80; retain Q84 as a falsifier and review Q85 for translation

Q79 before the remaining Q80 projects. Q80's exact two-stage Big-Match
self-similarity calculation is landed at `61106b1`; it does not supply the
universal finite-public routing-resistance or rank theorem. Split and state
those remaining projects separately. The zero-sum sub-case of Q80 Part C can reuse the existing
Mertens--Neyman criterion and Big Match machinery immediately.

Do not freeze a universal settlement API until the endogenous-target question
has survived Sorin's example and the chosen certificate semantics preserves
the branch cancellation exposed by Question 84. Questions 82--83 give
one-scale delivery and controlled-delivery boundaries. Question 85 now
supplies the missing player-free coupled-scale bridge, but its deterministic
part deliberately stops at nonclosed entrance viability and its randomized
criterion assumes fresh public randomization. Its data must still be lifted to
accuracy-indexed strategic delivery with endogenous randomness and deviation
safety. That lift, together with a sound cancellation-aware consumer, should
determine any eventual root interface, not vice versa.

### 7. Q76--78 generic portions, gated

Only after the re-review follow-ups resolve. The compiler is three
separate objects, not one:

- fixed-terminal-depth compiler — nearest (prototype exists, broken, see
  step 1);
- occurrence-sensitive early-stopping compiler — missing mathematics
  (stopped-tree Nash transfer), not routine engineering;
- semantic stopping — a separate Q63 consumer.

### 8. Guarded atlas audit last

Attempt the actual Q77 audit only when every failed gate has a consumed
alternative. A same-rank circular theorem whose premise contains the
desired certificate receives no closure credit.

### 9. Q121 exceptional-clock fallback: formalize by quantifier layer

Q121's new stationary fallback is a valid mathematical closure theorem only
under the all-tail/subgame-perfect hypothesis used by Q107. It must be split
into small reusable statements rather than recorded as a designated-phase
periodic-density theorem:

1. **One-active stationary cap.** For the stationary root with only player
   \(i\) quitting at hazard \(h>0\), prove the exact deterministic-time/Never
   caps
   \[
   B_i=\max\{0,r_i(\{i\})\},\qquad
   B_j=\max\{r_j(\{i\}),
      (1-h)r_j(\{j\})+h r_j(\{i,j\})\}\quad(j\ne i).
   \]
2. **Exceptional-tail collapse.** If the infinite probability that no
   opponent of \(i\) ever quits is positive and absorption is almost sure,
   condition on that event and prove
   \(|V_j^t-r_j(\{i\})|\le2M\eta_t\), where \(\eta_t\) is the residual
   probability that some opponent quits after \(t\).
3. **Current-root coupling.** Deleting every current hazard except
   \(y_i^t=h\) changes player \(j\)'s immediate-quit payoff by at most
   \(2M\eta_t\). Keep this as a coupling/total-variation lemma; do not bury it
   in the game-facing theorem.
4. **All-tail Nash adapter.** Apply the shifted-tail quit and Never
   inequalities to obtain the stationary exploitability bound
   \(\beta+4M\eta_t\), hence \(\beta+\zeta\) at a sufficiently late positive
   \(i\)-hazard. If some late hazard is one, route instead to the separate
   credible-First branch, including its off-path continuation.
5. **Scope guard.** Designated-phase optimality supplies none of the required
   late-tail inequalities. A credible First profile need not be a periodic
   product profile. Neither implication may appear as a convenience lemma.

The all-tail theorem closes Q107's exceptional seam mathematically; Part H's
designated-phase selection problem remains open. Current commits formalize
several scalar and behavior-deviation ingredients, but this ledger should not
mark the full adapter green until the event-tail, coupling, stationary-cap,
and shifted-Nash pieces are connected in one game-facing theorem.

### 10. Q121 singleton meshes: retain the explicit rate and its quantifiers

For a singleton-flow certificate with \(L\) arcs, terminal coefficient
\(A_*=Da_*\), joint cycle survival \(\rho<1\), and worst opponent survival
\(\bar\rho<1\), the finite-horizon consumer has the scalar form

\[
\mathrm{gap}_{N,m}\le \frac{A_*}{m}+\frac{B_*m}{N},
\qquad
B_*=ML\left((1-\rho)^{-1}+(1-\bar\rho)^{-1}\right).
\]

With \(m=\lceil\sqrt N\rceil\), this is at most
\((A_*+2B_*)/\sqrt N\), while delivery to the fixed phase-start value is at
most \(2ML/[(1-\rho)\sqrt N]\). Formalize the scalar inequality and keep the
game adapter separate. The profile here depends on \(N\): it is an anytime
rate family, not one fixed uniform-equilibrium strategy. The ordinary uniform
quantifier fixes \(m\) after choosing an accuracy and only then sends
\(N\to\infty\).

### 11. Q122--Q124 debt, invariant, and marked-boundary boundary

Several sharply scoped finite results are now landed. Commit 740cbfb proves, for
an actual terminal beta-Nash profile, that

\[
U_i+\beta\le-\delta
\quad\Longrightarrow\quad
\delta\le
M\bigl(1-\Pr(\text{all opponents of }i\text{ continue forever})\bigr).
\]

The probability is computed under the profile with player \(i\)'s own Quit
action deleted. This is the correct zero-density fence weight; ordinary time
occupation can send the same fence to zero.

The finite-law ledger is now:

1. **Exceptional square-norm rigidity — LANDED at `c9f89e1`.** The standalone
   finite weighted-law theorem assumes the exceptional Bellman equation and
   equality of current/successor squared-distance moments and proves
   \[
   \mathbb E[(2X-X^2)\|w-r(\{i\})\|^2]=0
   \]
   together with the sharp support conclusions: every positive-weight edge has
   equal endpoints, every positive-hazard such edge has both endpoints at the
   singleton value, and positive weighted mean hazard selects one concrete
   positive-hazard singleton-value edge. It does not construct the invariant
   law, derive the moment identity from game semantics, or assert ergodic
   component constancy.
2. **Common-hazard stationary fallback.** From one positive component hazard,
   derive every inactive inequality at the solo root and consume the existing
   arbitrary-deviation stationary cap theorem when
   \(r_i(\{i\})\ge0\).
3. **Dummy residual-game graft.** Formalize only its exact fixed-edge,
   stationary, Never, and stationary pure sure-First statements. Do not claim
   preservation of arbitrary First continuations; the dummy can be used off
   path as a fence.
4. **Marked finite law.** The first-opponent weights telescope exactly, and
   their normalized law has old-owner payoff moment at most \(-\delta\).
   Full quitter sets must remain in the state.
5. **Finite marked-packet selection — LANDED at `e0c7c08`.** From a normalized
   finite weighted packet with mean old-owner payoff at most \(-\theta\), the
   division-free theorem proves the
   \(\theta/(4M)\) good-boundary versus
   \(\theta/[4M(|I|-1)]\) fixed-player negative-transfer alternative.
   The actual first-opponent adapter and finite re-rooting iteration are landed
   through `01c2f69`; `b9d80d5` further separates same-date from
   strictly-later-date owner repeats.
6. **Summable-clock value limits — LANDED at `b271445` and `fa332a0`.** Finite
   total variation gives a value limit; active own Quit support identifies the
   current pure-Quit endpoint, and a limit strictly above the singleton reward
   forces eventual pure Continue.
7. **Minimum-debt costate — LANDED at `ea4354b`.** The playerwise clock loss
   times old debt is bounded by the specified prepend/minimum-debt drop. This
   is a certificate on that construction, not a proof that minimum debt
   vanishes and not an equilibrium nonexistence theorem.
8. **Zero-loss augmented edges — LANDED at `a79c2c7` and `e924c65`.** The first
   commit proves the all-Continue/solo support classification; the second
   proves compactness of the bounded augmented edge graph. Empirical-law
   invariance and Palm retention are not yet Lean theorems.
9. **Exact finite dynamic debt — LANDED at `ced42ed`.** The Q123-(111)
   recursion, nonnegativity, residual bound, and survival envelope are checked
   for supplied policy values and terminal debt. The module does not identify
   this finite quantity with unrestricted infinite-horizon exploitability or
   prove existence. `43c23a3` shows that a nonsummable supplied opponent clock
   discharges it from every fixed start when the local residuals vanish; it
   still does not construct a profile.
10. **Bounded-depth fourth branch — LANDED regression at `9ebc60a`.** Exact
    chains with cutoffs tending to infinity have a genuine same-date
    `IsActualTransfer` two-cycle whose residual depth is constantly two.
    Repeated labels therefore do not produce a temporal SCC.
11. **Projective escaping tail — LANDED at `6bde9c6`.** If residual depth
    genuinely tends to infinity, compactness extracts a chronologically
    compatible infinite exact debt tail; vanishing fixed-time losses give the
    zero-loss support classification. No hazard divergence, deviation
    semantics, or equilibrium conclusion is asserted.

The weak-limit marked-fence theorem is hand-proved but not yet in Lean. It
does not have equal current/successor marginals. Q123's Palm extraction is
also hand-proved and conditional: vanishing product/entropy defects give a
local hybrid absorption path, while terminal strategic validity additionally
requires every playerwise opponent clock to diverge. The corrected Q124
induction has four branches—finite discharge, new flag, repeated flag with
projective temporal/hazard escape, and bounded-depth unresolved terminal
packet. The player-indexed projective lift remains a construction question,
not a safe interface.

### Deferred

No admitted modules; no generic leaf-resolution structure whose field is
the final certificate; no exhaustive atlas dispatcher; no Uniform capstone
refactor. In particular, do not multiply the central `sorry` into endpoint-
preserving local `sorry`s: that interface is now known to be false.

## Standing discipline (carried forward, still in force)

- **Closed-output discipline**: semantic closure, concrete terminal public
  system, completely discharged realized account, or valid strictly lower
  children. Raw separators, mixed Farkas vectors, zero pairings,
  target/germ mismatches, failed calendars are not closed outputs. A mismatch
  may feed a proved root-retargeting construction, but it cannot be silently
  re-labelled as target preservation. An
  inert mixed certificate is closed only by a proved Route-0 theorem,
  never by silent discard.
- **Prefix versus shifted estimates**: every child-producing theorem
  labels its mechanism (root-prefix, shift-uniform, or legal restart).
- **Owner-history and signed-account discipline**: complete row lift,
  incidence, target/rebasing fibers, orientation, realization template
  retained; negative coefficients need exact or reverse-oriented ledgers;
  adapted coefficients need a sublinear switching term.
- **Acceptance criteria**: rigorously proved standalone theorem; adapters
  verify all hypotheses; no assumed final certificate; declared vs
  complete child libraries distinguished; prefix/shifted labels correct;
  provenance retained; direct consumer compiles without a new placeholder.
- **Endpoint discipline**: `germ.endpointValue` is analytic source data. No
  default coercion may turn it into the declared uniform target. Equality is a
  theorem in special classes, never a universal field.

The single admission remains `exists_uniformDeviationCapConstructor`
(Uniform.lean:207--211), proved equivalent in-file to the semantic
statement. The global result is complete only when the final theorem has
no dependency on sorryAx.
