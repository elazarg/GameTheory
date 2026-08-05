# Uniform-equilibrium project pipeline

**Production-Lean checkpoint:** `14d75ff`; **research-control checkpoint:**
`cd1db11`, both audited on 2026-08-03. **This file revised 2026-08-04.** Lean
work landing after the last audited commit is uncommitted-or-newer and not yet
reflected in these checkpoints.

This is project-control truth: decisions, dependency priorities, gates, and
acceptance conditions. It is not a mathematical exposition. The fixed-cutoff
holonomy compactness work is committed and counted; the marked absorption-path
route is a selected open design, not production mathematics. New Lean files are
never counted as landed until committed, built, and reflected in the owning
claim and [`FRONTIER.md`](FRONTIER.md).

**Handoff validation.** `lake build` succeeds. Local Markdown links under
`docs/`, `ideas/`, and `REORG.md` resolve. The stricter repository audit is
known red, not silently green: it reports four `opaque` declarations, ten
`native_decide` proofs, and 25 tracked Lean modules outside the default import
targets; the two intentional `sorry` declarations are
`exists_uniformDeviationCapConstructor` in `UniformExistenceConjecture.lean` and
`quittingGame_exists_uniformEquilibriumPayoff` in `QuittingConjecture.lean`.
These are owned by the engineering queue below and the [proof-engineering
audit](../../ephemeral/ProofEngineeringAudit.md), rather than blockers hidden in
the P0 mathematical status.

## How to maintain this file

Items are identified by ID and never renumbered. Status is a field on the item,
edited in place, not a location in the file -- moving an item between sections
is not how a status change is recorded. Finished items move to
[`PIPELINE-Archive.md`](PIPELINE-Archive.md) exactly once and never come back.

Being able to feel the work cycle at a glance is itself a design goal of the
status index below, which is why the index is grouped by cycle stage (ready,
active, partial/blocked, done) rather than by lane. This is a maintenance
convention, not a research priority, and it must never displace the mathematical
content it organizes.

## Status index

One line per item, grouped by work-cycle stage so what is ready, moving,
stalled, and finished is visible at a glance. Within a group, items are listed
lane by lane in the order they appear below.

**READY** — pick up now
- `MATH-P1-1` — re-derive Q148's encoding into the isolated-negative branch
- `MATH-P1-2` — test affine hazard domination on the exact-D families
- `LEAN-F0-1` — formalize the state-dependent-to-independent action-set padding
  reduction
- `LEAN-F0-2` — make the absorption fence structural, closing the all-continue
  vacuity trap
- `LEAN-F0-3` — bridge finite-horizon average to the liminf-average game
- `LEAN-F0-4` — construct the infinite-play measure by Kolmogorov extension
- `LEAN-F0-6` — package three implications used as self-evident
- `LEAN-P1-2` — define stationary regret and its zero/positive gap dichotomy
- `LEAN-P0-5` — formalize that signed phasewise accumulation equals
  relaxed-cycle gain
- `LEAN-P0-6` — prove the pure quit-time supremum equals the companion map's
  fixed point
- `LEAN-P2-2` — discharge three prose-only items the model-faithfulness audit
  found
- `LIT-P1-2` — complete the FTV source statement audit
- `LIT-P2-1` — define the positive-recursive nonrectangular theorem's repository
  adapter
- `LIT-P2-2` — separate Bewley-Kohlberg inputs from the independent Puiseux
  route
- `LIT-P2-3` — close the three residues of the borrowed-premise census
- `ENG-P0-1` — put CI under .github/workflows/ and make it green
- `ENG-P0-2` — make the axiom audit exact and add P0 keeper capstones
- `ENG-P1-1` — classify the 25 root-unreachable Lean modules and
  opaque/native_decide policy

**ACTIVE / IN FLIGHT**
- `MATH-P0-1` — prove compactness for generalized completed chronological traces
- `MATH-P0-2` — prove the robust pointwise alternative
  (augmented-AP-to-terminal-profile compiler)
- `MATH-P0-3` — exhaust the inexpensive repair ladder
- `MATH-P2-1` — turn a vanishing-discount APS family into a gain-bias packet
- `MATH-P2-4` — complete fixed public-controller rejection and bounded-template
  synthesis
- `NEG-P0-1` — certify a finite quitting table with a positive terminal
  exploitability gap
- `NEG-P1-1` — exact screens on rational four-player tables
- `LEAN-F0-5` — maintain the notion lattice and drive the F0 queue off it
- `LEAN-P1-1` — prove every two-player quitting game has stationary
  eps-equilibria
- `LEAN-P0-2` — formalize the two carrier refutations that exist only as prose
- `LIT-P1-4` — second round of reference-chain closure and flagged-item intake
- `ENG-P0-3` — run integration-sweep after every parallel-work wave, before
  committing
- `ENG-P1-2` — keep the pipeline/frontier and claim-level links clean and
  current

**PARTIAL / BLOCKED**
- `MATH-P1-3` — decide whether quitting is complete for the general conjecture
- `MATH-P2-2` — derive a positive global welfare separator, or refute the lift
- `MATH-P2-3` — route an analytic Bellman/value leaf through a strategic gate or
  obstruction
- `MATH-P2-5` — give exact-D anchors a digraph structure and test bounded loop
  erasure
- `LEAN-P1-3` — package Q132's exact behavioral nonattainment table
- `LEAN-P1-4` — define the finite marked absorption-cylinder encoding and its
  identities
- `LEAN-P2-1` — source-aligned FTV stationary-impossibility theorem
- `LIT-P1-1` — audit and formalize four-player fallback-collapse propositions
- `LIT-P1-3` — audit the Solan-Solan Q-matrix normalization for a quitting
  preprocessor

**DONE**
- `LEAN-P0-1` — landed debt-transport, cycle-mismatch, FTV, and germ-bridge
  results this cycle — see [archive](PIPELINE-Archive.md)
- `LEAN-P0-3` — pin the matching scaling case in the germ bridge — see
  [archive](PIPELINE-Archive.md)
- `LEAN-P0-4` — discharge nondegeneracy of the germ quit family — see
  [archive](PIPELINE-Archive.md)

## Project-control decisions

### `PC-001` — make finite quitting games the primary front

**Decision.** Make finite quitting games the primary direct mathematical front.

**Rationale.** They are a strict subclass, but a counterexample refutes the
universal conjecture and the positive problem now has an exhaustive
optimized-debt split.

**Rejected.** Treat every stochastic-game architecture as equal priority.

**Consequence.** General routes continue in parallel, but cannot displace the
quitting P0 hinge by recency.

**Revisit trigger.** A quitting solution that fails to lift, a certified
quitting counterexample, or a more upstream general reduction.

### `PC-002` — treat terminal existence, not uniformization, as the finite-quitting waist

**Decision.** Treat terminal approximate existence—not uniformization—as the
finite-quitting waist.

**Rationale.** Terminal existence iff uniform payoff is production Lean.

**Rejected.** Continue optimizing horizon-conversion constants as the main
problem.

**Consequence.** Every quitting proof/counterexample is evaluated at terminal
all-behavior exploitability.

**Revisit trigger.** A flaw in the formal bridge or a change of model.

### `PC-003` — escaping-middle compactification plus a repair decoder is the P0 hinge

**Decision.** The current P0 hinge is escaping-middle compactification plus a
repair decoder within the zero-pinned exact-`D` grammar; the fixed-debt-descent
alternative is closed — no bounded exact extension achieves a cutoff-independent
decrement (see [`AnchoredRepairOrUniformDebtDescent.md`][anchored-repair]).
**Tightness is no longer an alternative**: an explicit two-player weight has
optimized debt `1/8` at every cutoff with all mass escaping to a receding
terminal row, so the tails are not uniformly tight and no common truncation
length exists.

**Rationale.** Two endpoint charts, packet provenance, exact finite-block
holonomy, and now the full fixed-cutoff provenance lift are compact/closed. A
machine-checked length fence proves that literal unbounded game length cannot
live in any compact `ℕ × X` lift.

**Rejected.** Equate compact scalar coefficients—or fixed-cutoff closure—with a
compact bounded-cost executable repair relation.

**Consequence.** Add an infinity/stopping-law chart plus a separately bounded
finite decoder, or exhibit a calibrated incompatibility family. Uniform
middle-length tightness is no longer an admissible route.

**Revisit trigger.** A simpler repair closes every plateau, or a decisive
incompatibility chooses the necessary new state/route.

### `PC-004` — run repair ladder and counterexample CEGIS in parallel with the P0 route

**Decision.** Run a direct repair ladder and all-behavior counterexample CEGIS
in parallel with the P0 compactness route.

**Rationale.** Static/short repairs may close the plateau before general
geometry; the conjecture is universal, so a certified barrier is decisive.

**Rejected.** Wait for one grand positive proof before searching for
refutations.

**Consequence.** Stationary/full-set/short-word search exports exact violated
inequalities to the barrier lane; the descent lane is closed within the
zero-pinned grammar (see
[`AnchoredRepairOrUniformDebtDescent.md`][anchored-repair]).

**Revisit trigger.** One lane obtains an exhaustive certificate that subsumes
the others.

### `PC-005` — stop abstract work on the greedy buffered-path combinatorics

**Decision.** Stop abstract work on the greedy buffered-path combinatorics.

**Rationale.** Return/exit/dead-end is already checked; the missing theorem is
game-facing anchoring and decoding.

**Rejected.** Add more topology-only variants.

**Consequence.** E46 is mined infrastructure; work moves to relation semantics
and debt.

**Revisit trigger.** A decoder exposes a genuinely missing abstract
combinatorial premise.

### `PC-006` — separate scientific claims, literature, machine truth, and intake evidence

**Decision.** Separate internal scientific claims, attributed literature,
machine truth, and intake evidence.

**Rationale.** Diary/index-only state produced stale and conflicting claims.

**Rejected.** Keep an ephemeral frontier as the operative handoff.

**Consequence.** Claim files and literature result files become authoritative;
proof-mining/questions/experiments are evidence only.

**Revisit trigger.** A demonstrated maintenance failure in the hierarchy below.

### `PC-008` — deprioritize escaping-middle compactification pending the free-terminal test

**Decision.** **Deprioritize escaping-middle compactification pending the
free-terminal test.** `MATH-P0-1` and `LEAN-P1-4` drop to P1 until the optimized
debt over chains with a *free admissible* terminal continuation is decided.

**Rationale.** The entire P0 hinge is downstream of "the exact-D chain grammar
has a positive plateau". That premise looked like it might be about the grammar:
both plateau witnesses are two-player tables with equilibria, and the surgery
witness carries a machine-checked zero-gain array.

**The free-terminal test has now been answered by an unaudited, unformalized
solver's answer, and it splits (`M [reported]`).** Two candidate unpinnings
are rejected; the faithful formulation selects both the prescribed and the
deviating terminal values by zero-seeded repeated-period iteration. Under it
the surgery witness collapses to gap zero, but the weight
`r({1}) = r({2}) = (-1,1)`, `r({1,2}) = (1,-1)` has gap **exactly `1` at every
length** — so a gap can survive faithful unpinning, and compactification is
therefore **not** categorically work on an artifact. See
[`FaithfulUnpinningLeavesASurvivingGap.md`](../../ideas/PositivePlateauBoundaryClosure/FaithfulUnpinningLeavesASurvivingGap.md)
for the exact statement, the per-row seals (the "unpinning kills both known
plateau witnesses" sub-claim has independent machine-checked support; the
faithful-formulation content does not), and what would raise the seal.

**Rejected.** Continue building marked-cylinder semantics at P0 before knowing
whether the plateau survives unpinning.

**Consequence.** Escaping-middle work continues at P1 and is not abandoned; the
freed capacity goes to the free-terminal calibration and the zero-mismatch-cycle
question. If free-terminal debt stays positive on some weight, the compactness
lane returns to P0 with a target that is informative about the game.

**Revisit trigger.** The free-terminal test resolving either way, or a weight
exhibiting a plateau that survives unpinning.

### `PC-010` — PC-009's stated basis is established, at the bounded form (RESOLVED)

- **Status:** RESOLVED (2026-08-04)

**Decision.** **RESOLVED 2026-08-04 — `PC-009`'s stated basis is established, at
the bounded form.**

**Rationale.** The attributed theorem is E. Solan, *The dynamics of the Nash
correspondence and `n`-player stochastic games*, International Game Theory
Review **3**(4), 291–299 (2001), DOI
[`10.1142/S0219198901000488`](https://doi.org/10.1142/S0219198901000488),
**Theorem 2.1**; the game of its Figure 1 is the case-2 weight times `3`. Its
literal statement carries no boundedness hypothesis and is machine-checked
**false**; its proof runs through the convex-hull bound `Σ_i y_i ≤ 4`, which is
where boundedness enters unstated, so the bounded form is what is proved — and
the bounded form is what the finite-cycle deduction needs, since repeating a
cycle lands inside that hull. The case-2 row returns to `PROVED`. Full record:
[`PerturbedFTVGameHasNoBoundedCompletelyAbsorbingInverseIterate`](../../ideas/UniformEquilibriumLiterature/PerturbedFTVGameHasNoBoundedCompletelyAbsorbingInverseIterate.md).
The same paper's **Theorem 2.2** independently attests the diverging-period
claim. Original entry follows. The case-2 refutation was deduced from "this
weight admits no completely absorbing inverse iterate". That statement,
**without a boundedness condition on the values**, is false: an explicit iterate
has rows `(p,0,0)` and values `(1/3, 1, K·q^{-t})`, whose third coordinate grows
exactly like the inverse of the survival product, leaving an unconsumed
homogeneous boundary term. **Machine-checked** in
`QuittingUnboundedInverseIterate.lean`
(`not_noCompletelyAbsorbingInverseIterate`, for every `η ≥ 0`), with the
mechanism isolated as `survivalPrefix_mul_value_two`: the survival prefix times
the third value is a positive constant at every stage. Repetition of a finite
cycle does give bounded values, so the deduction to "no finite absorbing cyclic
array" would go through from the **bounded** form — stated separately as
`NoBoundedCompletelyAbsorbingInverseIterate`, recorded as the weaker claim, and
open.

**Rejected.** Treat the case-2 refutation as established, or discard `PC-009`
outright.

**Consequence.** The absorption-path route is **not** re-deprioritised:
`PC-009`'s other leg is independent of this. The conversion is available and the
period-`3m` family has vanishing gains, and that computation uses only the block
structure, survivals and defect asymptotic — not the attribution. So the carrier
being non-finite still has support; what lapses is the claim that a specific
weight admits *no* finite cycle.

**Revisit trigger.** **Audit returned 2026-08-04: `NOT LOCATABLE`.** No such
theorem was found under that attribution — every Solan quitting-game paper and
an arXiv author sweep were searched; none contains the cited terminology and
none of the quitting papers has a Theorem 2.1. Worse for the claim: the weight
at `η = 0` is the Flesch–Thuijsman–Vrieze cubic game divided by three on all
seven rows, and that game has an exact bounded absorbing complementary cycle of
length three — so the **bounded** form is false at `η = 0` too, and the entire
statement rests on the perturbation. The perturbation is aimed exactly at that
cycle and kills it on a knife-edge: the idle coordinate's gap is `η/6`, zero at
`η = 0` and positive after — matching the source's own scope, "for every `ε > 0`
sufficiently small", with no `ε_0` supplied. **Both sweeps missed the paper**
because its title names neither quitting games nor absorption and it is not
among the repository's local PDFs; the citation trail found it, as reference
`[16]` of Ashkenazi-Golan–Krasikov–Rainer–Solan. A source audit must chase the
reference lists of papers already on disk before returning `NOT LOCATABLE`, and
must sweep `ephemeral/` — noting that `sources/aps-quitting-2026.pdf` there is a
3 KB HTML bot-block page, not a paper.

### `PC-009` — reopen the absorption-path route; retire the finite-cycle carrier

**Decision.** **Reopen the absorption-path route; retire the finite-cycle
carrier.** Restore `MATH-P0-1` and `LEAN-P1-4` to P0, superseding `PC-008`'s
demotion.

**Rationale.** Finite absorbing complementary cycles are refuted as a complete
carrier in every open case: a three-coordinate weight with all diagonal entries
positive admits none of any length, and a case-3 weight is obstructed by an
isolated negative discounted limit. What does exist is a family of absorbing
cyclic recursions of period `3m` with complementarity defect of order `1/m`,
converging to a continuous mass-parametrized absorption path — marked, in case
3, by the isolated-coordinate mismatch. So the correct carrier provably is not
finite.

**Rejected.** Keep pursuing completeness of a finite-cycle disjunction, or keep
the absorption path deprioritised.

**Consequence.** The path work resumes with a sharper target than before: it
must carry the mass parametrization and the mark, and must supply the conversion
from a defect-`ε` recursion to an `ε`-approximate solution. The pin diagnosis,
and the tightness and surgery refutations built on the zero-pinned grammar, are
unaffected and do **not** come back.

**Revisit trigger.** The attributed external theorem underlying the case-2
refutation failing an audit — **that trigger is now spent: the theorem is
located and holds at the bounded form the deduction uses (`PC-010`), and the
same paper's Theorem 2.2 independently attests the diverging period**. The
conversion half of this trigger has since **fired favourably**: the signed
phasewise accumulation equals the gain exactly, so the conversion is available,
and it vanishes on the period-`3m` family, whose computation does *not* consume
the attribution. Two further constraints on the path follow: a scalar mass
parametrization is provably insufficient — it cannot distinguish a phase where
only the deviator is active from one where an opponent is — so the carrier must
retain the **ordered activity increments**, and the limit is stable only under a
uniform deleted-contraction margin.

### `PC-011` — decline result-graph; extend audit_repository.py instead

**Decision.** **Decline `result-graph` and any external declaration-graph tool
as build-gate infrastructure. Extend `scripts/audit_repository.py` instead.**

**Rationale.** The decisive argument is logical, not managerial. Lean's import
discipline means a module that is not imported cannot have any of its constants
named elsewhere, so a **module-level** import check is *equivalent* to the
declaration-level soundness fact wanted -- not an approximation of it. A heavier
declaration-graph tool would therefore answer no stronger question here.
Supporting: `audit_repository.py` (176 lines) already builds the tracked import
graph, already detects the 25 orphaned modules -- it is the source of that
figure -- and already flags `opaque`/`native_decide`/`axiom`/`unsafe`/`partial`.
The three real gaps are CI not wired under `.github/workflows/`, the axiom
audit's multiline-parser bug, and the unenforced leaf invariant; each is a small
targeted change to existing Python.

**Rejected.** Adopt a one-week-old, one-star personal project pinned to
`lean-toolchain v4.33.0-rc1` against this repository's `v4.32.2`, to answer a
question twenty lines of existing Python answers in under a second.

**Consequence.** Make the **leaf invariant build-checkable**: invert the
existing forward import dict and assert that the importers of the two
`sorry`-carrying modules are contained in `{root aggregator, each other}`.
Independently verified today: importers of `QuittingConjecture` are
`{GameTheory}`, importers of `UniformExistenceConjecture` are
`{GameTheory, QuittingConjecture}`. **The check must also assert the root
aggregator declares nothing**, since the root does import both and the
equivalence argument only holds for a pure import list.

**Revisit trigger.** The tool becoming maintained and toolchain-compatible *and*
a question arising that genuinely needs declaration-level rather than
module-level resolution. Note the decline rests partly on unverified ground: the
toolchain mismatch and the no-install fence meant nobody confirmed
`result-graph` runs here at all.

### `LEAN-F0-7` — the tail-average transfer is mirrored, not doubled

- **Status:** DONE
- **Lane:** F0
- **Depends:** `LiminfAverageBridge`, `InfinitePlayMeasure`.
- **Record:** [Notion lattice](NotionLattice.md)

**Objective.** Settle how `IsUniformEquilibriumPayoff` transfers to the
tail-average notions, and record the limsup node the registry lacked.

**State.** Landed, and it refutes the framing this row was opened with. That
framing said the liminf on-path failure signals liminf is the wrong target,
with limsup getting **both** directions free. Only half is right.

Negation exchanges the two limits unconditionally, so each abstract lemma
dualizes with no change to the `ENNReal`/Fatou internals. But dualizing the
*conditional* lemma yields a *conditional* statement: the almost-sure
hypothesis is relabelled, not removed. The moving-bump family dualizes too,
refuting the unconditional limsup-deviation bound exactly as the original
refutes the unconditional liminf-on-path bound.

So the split is **mirrored**: liminf gives the deviation direction free and the
on-path direction conditional; limsup gives the on-path direction free and the
deviation direction conditional. Neither tail notion is the uniform notion's
"natural home" — each buys one direction and owes the other. Both game
corollaries are free of any representation hypothesis, since they run on the
landed play measure.

**Acceptance.** The two-directional limsup transfer as a named theorem, the
limsup node and its edges in the registry, and the liminf edges restated as the
conditional ones they are. Cheapest adjacent item: formalize the
typewriter/moving-bump family, converting the registry's FALSE-by-reason edge
into FALSE-by-machine.

### `LEAN-F0-8` — the bounded-transversality lemma behind the case-2 repair

- **Status:** READY
- **Lane:** F0
- **Depends:** `QuittingUnboundedInverseIterate`.
- **Record:** [Perturbed FTV inverse iterate][perturbed-ftv]

**Objective.** Prove that a bounded completely-absorbing iterate has vanishing
survival-weighted value: `|values| ≤ M` and completely absorbing imply
`survivalPrefix · value → 0`. Reportedly three lines by squeeze.

**State.** The published theorem this program depends on is false as printed,
and holds in the bounded form. That bounded form is currently prose plus an
unused `Prop` placeholder that is never established and never consumed — while
the only formal artifact in the file *refutes a different statement*. The
mechanism is exactly failure of transversality of the homogeneous boundary
term: the witness keeps `survivalPrefix · value` at a nonzero constant while
the survival prefix vanishes.

The honest repair of the source's step is strictly weaker than boundedness —
"the homogeneous boundary term vanishes". Nobody has attempted that
re-derivation. The same phenomenon governs whether a periodic deviation
recursion determines its continuation value at all: when the survival product
fails to decay the fixed set is a ray, and the recursion selects nothing.

**Acceptance.** The squeeze lemma landed, the `Prop` placeholder either
established or removed, and the case-2 row resting on a formal artifact that
proves the statement it cites.

### `PC-007` — keep one formalization lane active whenever source-ready mathematics exists

**Decision.** Keep one formalization lane active whenever source-ready
mathematics exists.

**Rationale.** Formalization catches quantifier/model errors and the backlog is
substantial.

**Rejected.** Pause Lean until a conjecture breakthrough.

**Consequence.** Two-player quitting existence and stationary gap packaging
remain active even while P0 mathematics is open.

**Revisit trigger.** No honest formalization-ready result remains.

## Conjecture-closing mathematics

### `MATH-P0-1` — prove compactness for generalized completed chronological traces

- **Status:** ACTIVE
- **Lane:** P0
- **Depends:** `QuittingBoundaryHolonomy`,
  `QuittingBoundaryHolonomyCompactness`, two-ended packet, calibrated minimizer
  provenance.
- **Record:** [Realized anchored holonomy
  closedness](../../ideas/PositivePlateauBoundaryClosure/RealizedAnchoredHolonomyClosedness.md),
  [the carrier claim](../../ideas/PositivePlateauBoundaryClosure/CompletedVectorFactorTraceIsCompactAndDetermining.md),
  [the aggregated-carrier fence](../../ideas/PositivePlateauBoundaryClosure/AggregatedCarrierConflatesOriginValues.md),
  [enriched absorption paths][ep], [cylinder design
  note](design/MarkedAbsorptionCylinder.md)

**Objective.** Prove a compactness theorem for **generalized completed
chronological traces** with finite calibrated blocks dense in them, carrying
exit-or-Never mass, anchors, the conditional packet, payoff, the completed
stopping-obstacle hypograph, deleted-clock graphs, and debt.

**State.** `ACTIVE` at **P0**: `PC-009` restored this lane, superseding
`PC-008`'s demotion. Finite semantics and fixed-cutoff closure are landed.
Closure of the finite realized set is refuted, and no sequentially compact added
coordinate can close it with continuous projection. Completed chronological
graphs supply ambient compactness, a continuous cap with retained witness,
closed anchored splice, and continuous concatenation. **A carrier construction
is claimed settled (`M [reported]`, 2026-08-04) — unaudited, unformalized.**
Take `𝔗_r` = the closure of the joint completed **vector-factor** trace
`t ↦ (τ(t), (P_j(t))_j)` together with the joint obstacle hypographs; the
claim is that it is compact and determining with no compactness-versus-
determination trade-off, finite complementary arrays dense, and every object
pulling back simultaneously in trace, cap, and origin value. See
[`CompletedVectorFactorTraceIsCompactAndDetermining.md`](../../ideas/PositivePlateauBoundaryClosure/CompletedVectorFactorTraceIsCompactAndDetermining.md)
for the exact statement, the two load-bearing conventions (piecewise-affine
completion; fixed terminal vector), and what would raise the seal.

**Acceptance.** Build `𝔗_r` and the exact finite adapter against it. Do **not**
pursue a missing-compact-coordinate closure of the finite set; that shape is
impossible. Do **not** fall back on the aggregated carrier: its fibres can carry
*different origin values* at the same obstacle trace (`M [reported]`; see
[`AggregatedCarrierConflatesOriginValues.md`](../../ideas/PositivePlateauBoundaryClosure/AggregatedCarrierConflatesOriginValues.md)),
so aggregation is not harmless.

### `MATH-P0-4` — map AGKRS Theorem 3.4 clause by clause against the internal trichotomy

- **Status:** READY
- **Lane:** P0
- **Depends:** `QuittingThreeBranchDisjunction`; AGKRS Theorem 3.4 and its two
  sources.
- **Record:** [carrier group](../../ideas/AbsorbingCycleCarrier/README.md)

**Objective.** AGKRS Theorem 3.4 is a published **iff**: `ε`-equilibria for
every `ε` hold exactly when (S.1) ∨ (S.2) ∨ (S.3). The internal three-branch
disjunction is machine-checked. Map the clauses against each other — is
zero-solo (S.1)? is the admissible cycle (S.3)? what is (S.2) internally?

**State.** If the trichotomies align, the published iff says something much
sharper than anything currently claimed: **completeness of the internal
disjunction is equivalent to the quitting conjecture**, which re-types the
third branch's sufficiency question as the exact published boundary rather
than as one open disjunct among three.

**Fence — records now exist, mapping still does not.** Both sources are
recorded in `references/20-nonzero-sum-equilibrium.md`. Solan–Vieille 2001
Prop. 2.13 is `[primary]` — full text of both the working paper and the
published version read; it turned out to be a terminal-payoff/uniform-
equilibrium **bridge lemma**, not a structural characterization, and its
numbering does not exist in the 1998 working paper at all (added at
publication). Simon 2007 is genuinely paywalled and remains `[unverified]`/
`[secondary]` at best — abstract-level content only, no primary read of
"Theorem 3" itself. Since Prop. 2.13 is now known *not* to carry the S.1/S.2/
S.3 content, Simon 2007's Theorem 3 is the more load-bearing of the two for
the clause map below, and it is the one still unread. Do not consume Theorem
3.4's *characterization* content before Simon 2007's Theorem 3 is obtained in
full; the borrowed-premise pattern is only half-defused.

**Acceptance.** A clause-by-clause map with each correspondence either proved,
refuted, or explicitly open, plus wing records for whichever source the
argument leans on.

### `MATH-P1-4` — formalize the weight whose gap survives faithful unpinning

- **Status:** READY
- **Lane:** P1
- **Depends:** the free-terminal formulation (zero-seeded repeated-period
  iteration of both terminal values); existing two-player table machinery.
- **Record:** [`FaithfulUnpinningLeavesASurvivingGap.md`](../../ideas/PositivePlateauBoundaryClosure/FaithfulUnpinningLeavesASurvivingGap.md)

**Objective.** Machine-check that `r({1}) = r({2}) = (-1,1)`,
`r({1,2}) = (1,-1)` has free-terminal optimum exactly `1` at every length, and
that the surgery witness `r({1}) = (a,0)`, `r({2}) = (1,-1)`,
`r({1,2}) = (0,1)` has optimum `0` at every length.

**State.** This is the first weight whose gap is not a terminal-pinning
artifact, so it is the first honest instance of the hard case. The pair is
worth landing together: one weight collapses under faithful unpinning and one
does not, which is exactly the separation the pinned formulation could not see.
Reported structure: the surviving gap is a negative singleton value carried by
the unique active coordinate.

**Acceptance.** Both computations machine-checked, with the free-terminal
formulation itself defined in Lean rather than assumed. Translate carefully —
the pinned-versus-free distinction is precisely where earlier de-gamed
transcriptions went wrong, and a matched terminal pair gives zero on every
weight.

### `MATH-P0-2` — prove the robust pointwise alternative (augmented-AP-to-terminal-profile compiler)

- **Status:** ACTIVE
- **Lane:** P0
- **Depends:** `MATH-P0-1`, corrected full-jump continuation semantics, E40,
  E46, E47, exact root construction.
- **Record:** [Anchored repair or descent][anchored-repair], [enriched
  absorption paths][ep], [the relaxed-limit
  fence](../../ideas/PositivePlateauBoundaryClosure/RelaxedLimitPackageDoesNotCertifySmallGain.md)

**Objective.** Prove the robust pointwise alternative: a corrected
augmented-AP-to-terminal-profile compiler, within the zero-pinned exact-`D`
grammar. The bounded-finite-surgery cutoff-independent-debt-descent alternative
at the original root is closed (see
[`AnchoredRepairOrUniformDebtDescent.md`][anchored-repair]); uniformize the
surviving repair branch by sequential compactness.

**The limit-object route to this is closed as posed (`M [reported]`).** An
unaudited, unformalized solver's answer claims: the carrier of
`MATH-P0-1` is a valid closed *description* of relaxed limits, but the relaxed
package is **not a local certificate of approximate solutions** — value-
approximation and gain-approximation come apart, with an explicit finite
complementary witness carrying a robust gain floor that the chronological-
profile mark does not repair. See
[`RelaxedLimitPackageDoesNotCertifySmallGain.md`](../../ideas/PositivePlateauBoundaryClosure/RelaxedLimitPackageDoesNotCertifySmallGain.md)
for the exact witness, scope, and what would raise the seal. This does
**not** refute existence — a finite array with positive gain is unremarkable;
what it refutes is that trace-nearness transports low gain.

**State.** `ACTIVE`; the abstract buffered-path trichotomy is complete, but
neither game-facing decoder nor its local stability theorem is proved.

**Acceptance.** For fixed accuracy and positive debt threshold, every limit
state has one stable finite repair certificate or fixed local `L_z,c_z>0`;
sequential contradiction produces uniform `L,c`, terminal approximate profiles,
or contradicts the plateau.

### `MATH-P0-3` — exhaust the inexpensive repair ladder

- **Status:** ACTIVE
- **Lane:** P0
- **Depends:** Exact stationary caps, owner/joiner obstruction, fixed-word
  holonomy acceptance.
- **Record:** [Stationary
  repair](../../ideas/StationaryRepairExhaustion/README.md), [plateau repair
  fences](../../ideas/PositivePlateauBoundaryClosure/RepairAndClosureShortcutsAreFalse.md)

**Objective.** Exhaust the inexpensive repair ladder: cutoff-one, full
stationary set, quitter sets/pairs, and short accepted holonomy words.

**State.** `ACTIVE` parallel lane; no finite grammar is assumed complete.

**Acceptance.** Produce an actual repair, or a uniform violated inequality
consumable by `MATH-P0-2`/welfare separation.

### `MATH-P1-1` — re-derive Q148's encoding into the isolated-negative branch

- **Status:** READY
- **Lane:** P1
- **Depends:** Q148's normal form of the isolated cycle; `K1`–`K2`.
- **Record:** [carrier group](../../ideas/AbsorbingCycleCarrier/README.md)

**Objective.** Re-derive Q148's encoding — an arbitrary weight admitting no
absorbing cycle becomes an isolated-negative weight by adding one coordinate —
and settle its arity behaviour.

**State.** `READY`. If the encoding holds, the isolated-negative branch is
**complete** for the conjecture at the terminal-approximate waist: general
existence iff existence on the branch. Two things must be established before it
is stated as a theorem. (a) The encoding is `[reported]` — Q148's own convention
forbids resting on that without re-derivation. (b) It **adds a coordinate**, so
on its face it gives completeness of the branch *over all player counts* for the
problem *over all player counts*, **not** a fixed-`n` reduction — which matters
because the live attack is inductive with `n ≤ 3` settled.

**Acceptance.** Two consequences, both worth having independently of the
conjecture. It retires "complete the trichotomy by filling its third branch" as
a route — that branch is the whole problem, not a residual case. And it licenses
`NEG-P0-1` to restrict its search to the isolated-negative branch **without loss
of generality**, since a counterexample anywhere yields one in the branch.

**Evidence from the sharpest concrete instance (`M+L`, 2026-08-05).** The
program's only weight provably in the third branch **alone** — not zero-solo, no
admissible cycle of any period, isolated-negative present — **is repairable**,
and the repair delivers the real `IsUniformEquilibriumPayoff`, machine-checked
(`QuittingDisjunctionCounterexampleRepair.lean`). Its isolated mismatch is
exactly `1 = -r_2({2})`, and `δ = 0`: no positive floor exists against all
behaviour on this weight.

The mechanism is the structurally interesting part. The exact isolated witness
sits at survival slope `1`, in the fixed-point-ray regime, where the honest
value `-1` is dominated by the boundary payoff `0` of never quitting — a genuine
gain-`1` deviation. The repair **leaves the isolated regime entirely**: both
coordinates play the same constant hazard, so nothing is isolated and the ray
never arises, giving gains `≤ 2p` and an `ε`-equilibrium at `p = min(ε/2, 1)`.

So on this instance the obstruction is an artifact of insisting on the exact
isolated cycle, and repair is found by moving off it. That is consistent with
the separate result that a floor exists *within* exact complementarity: the two
together say the approximate equilibria are real but do not live in the
complementary grammar. **No general sufficiency theorem follows** — the
symmetric-coin construction is specific to this table.

### `MATH-P1-2` — test affine hazard domination on the exact-D families

- **Status:** READY
- **Lane:** P1
- **Depends:** Q149's power-comparison margin; the exact-`D` chain families.
- **Record:** [carrier group](../../ideas/AbsorbingCycleCarrier/README.md)

**Objective.** Test **affine hazard domination** on the actual exact-`D`
families: does `H_i <= alpha * H_{-i} + B` hold, with `H` the cumulative
hazards?

**State.** `READY`. Q149 settles what a deleted/full margin must look like. A
*difference* margin is vacuous: since `c <= c_{-i}` always, `1-c_{-i} <= 1-c`
holds trivially with constant one, so no array violates it. The genuine form is
multiplicative -- `c_{-i}(x_t) <= exp(b_{t,i}) * c(x_t)^theta` with
`sum_t b_{t,i} <= B`, giving `S_{-i} <= exp(B) * S^theta` -- and cumulatively
that is exactly affine hazard domination. A rowwise ratio `c_{-i} <= K*c` is
restored by `x_i <= 1 - 1/K` but yields only `S_{-i} <= K^m * S`, useful only if
the number of contributing stages is uniformly bounded. **The two genuine
obstructions are named**: a unique cumulatively saturated coordinate, or
unbounded imbalance `sup_x H_i/(1+H_{-i}) = infinity`.

**Acceptance.** A verdict on whether the exact-`D` families satisfy affine
hazard domination, or exhibit one of the two named failure modes. This is a
checkable property of a known family, not a research programme.

### `MATH-P1-3` — decide whether quitting is complete for the general conjecture

- **Status:** BLOCKED
- **Lane:** P1
- **Depends:** Q148's encoding technique (`MATH-P1-1`); the padding reduction
  (`LEAN-F0-1`); the class/player-count table in the literature wing.
- **Record:** [conjecture group](../../ideas/QuittingGameConjecture/README.md)

**Objective.** Decide whether a structured class -- quitting, or a bounded
family of classes -- is **complete** for the general uniform conjecture: does an
arbitrary finite stochastic game encode into it preserving
approximate-equilibrium existence?

**State.** `BLOCKED` on `MATH-P1-1`. Every known implication runs from the
larger class to the smaller -- absorbing solved gives quitting solved -- and no
converse lift is known. `PC-001` makes quitting the primary front without
claiming one, and lists ``a quitting solution that fails to lift'' as its own
revisit trigger, so this is the recorded main risk of the current strategy
rather than a new concern. Q148 supplies the only encoding technique in hand,
one level down: a branch that looked residual was shown to encode the whole
problem by adding a coordinate. Held until that encoding survives re-derivation,
since posing this on a `[reported]` premise is how two earlier questions were
built on false foundations. Prior expectation is that quitting alone is **not**
complete -- it discards recurrent structure, where a general game's difficulty
lives -- so the bounded-family form is the one to ask.

**Acceptance.** Either a completeness theorem turning `PC-001` from a bet into a
consequence, or a demonstration that no such encoding exists, which makes the
lift a separate open problem that must be named and scheduled rather than
assumed.

### `MATH-P2-1` — turn a vanishing-discount APS family into a gain-bias packet

- **Status:** ACTIVE
- **Lane:** P2
- **Depends:** Stable support/domain or resolved singular scales.
- **Record:** [Vanishing-discount synthesis][gbp]

**Objective.** Turn one controlled vanishing-discount APS family into a
split-domain gain--bias packet.

**State.** `ACTIVE`, downstream; no general family producer.

**Acceptance.** Source-aligned packet consumed by semantic credibility, or a
chattering counterexample fixes scope.

### `MATH-P2-2` — derive a positive global welfare separator, or refute the lift

- **Status:** PENDING
- **Lane:** P2
- **Depends:** Global occupation polytope and local failure data.
- **Record:** [Positive welfare separator][welf]

**Objective.** Derive a strictly positive global welfare separator from robust
repair failure, or refute that lift.

**State.** `PENDING`; positivity/globality not supplied by local Farkas
separation.

**Acceptance.** Positive Bellman bias feeds landed security/welfare assembly, or
a small exact sign counterexample closes the general route.

### `MATH-P2-3` — route an analytic Bellman/value leaf through a strategic gate or obstruction

- **Status:** PENDING
- **Lane:** P2
- **Depends:** Selected target, source-aligned analytic leaf, exact
  support/domain.
- **Record:** [Analytic-leaf gate or
  alternative](../../ideas/AnalyticLeafRouting/AnalyticLeavesNeedGateOrAlternative.md)

**Objective.** Route one actual analytic Bellman/value leaf through a named
strategic gate or a consumed closure/obstruction alternative.

**State.** `PENDING`; analytic germs can fail zero holonomy, and no universal
router/target selector exists.

**Acceptance.** A concrete leaf reaches a production credibility/compiler
interface, or its typed obstruction forces a proved alternative.

### `MATH-P2-4` — complete fixed public-controller rejection and bounded-template synthesis

- **Status:** ACTIVE
- **Lane:** P2
- **Depends:** Public controller skeleton, reachable-arena convention,
  gain--bias verifier.
- **Record:** [Bounded public-controller
  synthesis](../../ideas/BoundedPublicControllerSynthesis/FixedPublicControllersAreVerifiableButNotKnownComplete.md)

**Objective.** Complete fixed public-controller rejection and bounded-template
synthesis at each supplied size.

**State.** `ACTIVE` P2; finite-public completeness is false, clocked-private
completeness open (Q94), and no total computable public-node bound is
source-conditionally available (Q98).

**Acceptance.** Fixed-`K` accept/reject certificates with exact scope; never
infer all-size failure or unrestricted coverage.

### `MATH-P2-5` — give exact-D anchors a digraph structure and test bounded loop erasure

- **Status:** PENDING (inferred; source has no explicit status tag here)
- **Lane:** P2
- **Depends:** Anchor space and the admissibility relation
  `out(ℓ_k) = in(ℓ_{k+1})`; `Math/BoundedDiscrepancyCirculation.lean`'s `Walk`.
- **Record:** [Anchored repair or descent][anchored-repair], [bounded
  reachability
  depth](../../ideas/PositivePlateauBoundaryClosure/AnchoredShorteningFailsUnderDeterminedAnchors.md)

**Objective.** Give the exact-`D` anchors a digraph structure and decide whether
admissible words admit **bounded loop erasure**: a deletion bound `D` with
shortening `L(ε) ≤ N(ε/4) + D` at fixed endpoints.

**State.** `P2`, **not yet imported**. Anchored shortening at fixed endpoints is
a reachability question — exact endpoint fibers can have unbounded depth, and
this survives compact letter sets with continuous, injective, locally open
anchor maps and uniformly summable defects, so injectivity and local openness
are not the missing hypotheses. A finite anchor space or a bounded-deletion
property restores it. **Answered negatively for determined anchors (Q141,
`M [reported]`, unaudited and unformalized)**: exact-endpoint shortening is
false, and bounded depth uniform in the weight is false already at three
coordinates; for one fixed weight it holds only nonuniformly. See
[`AnchoredShorteningFailsUnderDeterminedAnchors.md`](../../ideas/PositivePlateauBoundaryClosure/AnchoredShorteningFailsUnderDeterminedAnchors.md)
for the exact statement, the two counterexample weights, and what would raise
the seal. So this row is no longer about whether shortening holds; it is
about whether any usable weaker form survives. The repository has no digraph
over anchors to state the property about; Mathlib's graph API is unused in
the quitting tree, and the two existing uses (`QuittingRefutedRouteFences`'s
`BlockingDigraphUnsolvable`, and the hand-rolled `Walk`) are one-offs.

**Acceptance.** Either a bounded-deletion theorem over the actual exact-`D`
anchors, or a demonstration that their fibers are thin and the question does not
transfer. **Promote to P1** only if a repair decoder is shown to consume one of
the surviving weak forms — the nonuniform fixed-weight bound, or the `O(1/ε)`
prefix approximation of a distinguished orbit. Note approximate internal
excision is *not* generally valid: the exact join and complementarity are
unstable.

## Refutation lane

### `NEG-P0-1` — certify a finite quitting table with a positive terminal exploitability gap

- **Status:** ACTIVE CEGIS
- **Lane:** P0
- **Depends:** Stopping-law semantics, terminal-to-uniform nonexistence bridge,
  exhaustive barrier language/rank.
- **Record:** [Counterexample acceptance][cex]

**Objective.** Certified finite quitting table with terminal exploitability gap
`δ>0` against every behavioral profile.

**State.** `ACTIVE CEGIS`; current screens exclude only subclasses.

**Acceptance.** One fixed positive all-behavior gap refutes the quitting and
general conjectures.

### `NEG-P1-1` — exact screens on rational four-player tables

- **Status:** ACTIVE
- **Lane:** P1
- **Depends:** E37/E39/E48-style inequalities.
- **Record:** [Counterexample acceptance][cex] plus [four-player literature
  fence](../../ideas/UniformEquilibriumLiterature/FourPlayerQuittingFallbacksFail.md)

**Objective.** Exact screens combining owner joining obstruction,
coalition-friction fence, and stationary gap on rational four-player tables.

**State.** `ACTIVE` experiment lane; not exhaustive.

**Acceptance.** Reject tables cheaply or feed survivors to longer
behavioral/barrier search.

## Lean formalization lane

### `LEAN-F0-1` — formalize the state-dependent-to-independent action-set padding reduction

- **Status:** READY
- **Lane:** F0
- **Depends:** `StochasticGame`, `IsUniformEquilibriumPayoff`.
- **Record:** this file

**Objective.** **Foundations.** Formalize the padding reduction from
state-dependent to state-independent action sets, so that
`exists_uniformDeviationCapConstructor` states the conjecture for every finite
stochastic game rather than for the state-independent class only.

**State.** `READY`. The type is `Act : ι → Type`; the field docstring previously
claimed it "may depend on state", which was false and is now corrected. The
reduction is standard — every player gets every action everywhere, illegal
actions inheriting the payoff and transition of a fixed legal one — and
preserves `ε`-equilibria in both directions. Quitting games are unaffected
(`Act = Bool` everywhere).

**Acceptance.** **PARTIAL, 2026-08-04.** The reduction's mathematical content is
landed in `ActionLegalityNormalization.lean`: a legality predicate with nonempty
legal sets, the normalization replacing illegal components, agreement with the
original stage payoff and transition on jointly-legal profiles, and the transfer
of an epsilon-Nash profile from the normalized game to the legality-constrained
one. **It does not discharge the row's acceptance condition.** `StochasticGame`
carries only `IsMarkovNash` -- exact, no epsilon -- so the transfer is proved
against a locally-defined Markov epsilon-Nash notion, not against the
behaviour-strategy notion `IsUniformEquilibriumPayoff` actually uses, which is
built on the heavier `BehaviorProfile`/`Hist` machinery in `Uniform.lean`.
**The converse splits by level, and the split is now settled at the lower one.**

*Markov level: PROVED.* `isεNormalizedMarkovNash_of_legal`
(`ActionLegalityMarkovConverse.lean`) closes it. The observability worry cannot
arise here for two independent reasons. `MarkovProfile` has no history
argument, and both notions are single-stage payoff comparisons with no
continuation, so a signal received earlier has no channel to a later decision.
And structurally, `normalizeAct` sends **every** illegal action at a state to
the *same* chosen legal one, so two distinct illegal actions are never
distinguishable to `normStagePayoff` at all.

*Behaviour level: OPEN, and still suspected FALSE.* This is where the reduction
actually needs the converse, and where the worry is real: histories record the
*raw* joint action played (`StageRecord = Fin t -> State x JointAct`,
`Basic.lean:61`). In the padded game every action is legal and payoff-equivalent
under normalization, yet the history still distinguishes which was played — so
the labels are free public signalling, which can *enlarge* the set of
history-dependent equilibria and break exactly the needed direction.

Building the separating game there needs two objects the repository lacks: a
normalized `StochasticGame` presentation, and a legality-constrained analogue
of `IsUniformEquilibriumPayoff` over legal behaviour profiles.

**The candidate repairs are not equal, and the choice is now decided (`M`).**

*Normalized-action histories* is the load-bearing one. Under it the padded
game's histories become literally the legal game's histories, so **every**
equilibrium transports definitionally, with no selection step.

*Normalization-invariant strategies* does not substitute. Restricting the
**deviator** to invariant strategies is unsound outright — the uniform cap
quantifies over all behaviour, and a restricted cap is a strategy-class-scoped
theorem, which this program polices. Restricting only the **prescribed**
profile does kill the channel: if no coordinate reads labels and payoffs and
transitions factor through the quotient, the deviator's label choice reaches
nothing. But the converse must transport an *arbitrary* padded-game
equilibrium, while invariance transports only invariant ones — so it needs an
invariant-selection theorem ("any equilibrium implies an invariant one"), which
is symmetrization over the label groupoid and runs straight into the recorded
non-convexity fence: Nash sets are not convex, so averaging equilibrium arcs
fails (`ideas/wild/RepresentationTheory.md:38`). Profile invariance is at best a
synthesis-side convenience whose completeness costs an unproved and probably
false-in-general step.

Consistency check: the Markov-level converse holds precisely because the
profile type carries no history — the channel does not exist there. That is the
mechanism's degenerate case, and it confirms the history *is* the channel.

Until normalized-action histories land, the conjecture is still formally stated
for the state-independent class.

### `LEAN-F0-2` — make the absorption fence structural, closing the all-continue vacuity trap

- **Status:** READY
- **Lane:** F0
- **Depends:** `IsεQuittingRootSuccessorCertificate`,
  `IsQuittingCyclicContinuationBlock`.
- **Record:** this file

**Objective.** **Foundations.** Make the absorption fence *structural*: install
a realizable-continuation wrapper accepted by every semantic consumer, which no
`tail`-parameterized theorem can bypass. Do **not** bundle absorption into each
local successor certificate: individual non-absorbing successor rows are
legitimate, and the positive-absorption condition is global over a cyclic block,
already expressed there (`QuittingCyclePinnedDebt.lean:143`). Bundling it
locally would distort the mathematics, and the type-error guarantee holds only
if weaker raw predicates cannot bypass the consumer interface. A wrapper that no
`tail`-parameterized theorem can bypass.

**State.** `READY`. `quittingRootSuccessorPayoff reward z allContinueRoot = z`
holds for **every** `z`, so the all-continue row satisfies the successor
equation against any continuation. Two mechanisms currently prevent vacuity —
the absorption clause of `IsQuittingCyclicContinuationBlock` and zero-anchoring
at a cutoff — and both are proved necessary (`quittingAllContinueBlock_forced`,
`not_isQuittingCyclicContinuationBlock_allContinueBlock`). But they are
per-theorem side conditions carried across the whole quitting tree, so a new
certificate omitting both reintroduces the trap silently and passes every
existing test.

**Acceptance.** Vacuity becomes a type error instead of a missing hypothesis.
This trap has been rediscovered independently five or more times.

**PARTIAL.** `QuittingRealizedContinuation` (in `QuittingCyclePinnedDebt.lean`)
bundles the absorption obligation as a field, with `ofBlock` as the
cheap-migration constructor, unbundling companions, and the regression that the
all-continue block does not inhabit it — reusing the existing forced-block
lemmas rather than reproving them. The tree's headline consumer is migrated,
plus an end-to-end re-derivation through the constructor.

**The type-error guarantee is not yet achieved, and the gap is precise.** Three
routes still bypass the interface. Every theorem still taking the raw
`IsQuittingCyclicContinuationBlock` remains callable — the original headline
theorem is deliberately kept, since three modules depend on it, and the
isolated-coordinate, mismatch-contraction, periodic-extension, and
disjunction-counterexample files are unmigrated. A future author can define a
look-alike predicate omitting absorption and write new theorems against that.
And the genuinely `tail`-generic per-row certificate is correctly left alone,
so hand-chained certificates can still be fed to any unmigrated consumer.

So the fence holds for signatures written to require the wrapper and nowhere
else. Closing it means migrating the remaining consumers, which is mechanical
but touches five files.

### `LEAN-F0-3` — bridge finite-horizon average to the liminf-average game

- **Status:** READY
- **Lane:** F0
- **Depends:** `IsUniformEquilibriumPayoff`, `finiteAveragePayoff`.
- **Record:** [Simon retraction
  audit](audits/2026-08-04-SimonMousetrapRetraction.md)

**Objective.** **Foundations.** Bridge the finite-horizon-average notion to the
liminf-average game: prove `E_σ[liminf_T A_T] ≥ v_i − ε` from a uniform
equilibrium payoff, or identify what extra hypothesis it needs.

**State.** `READY`. `IsUniformEquilibriumPayoff` constrains only finite-horizon
averages `finiteAveragePayoff s₀ T σ` for `T ≥ T₀`. The deviation direction
bridges by Fatou (`E[liminf A_T] ≤ liminf E[A_T]`); the **on-path** direction
does not follow from pinned expectations alone. So a non-existence theorem for
the liminf-average game does not formally refute our statement without this
lemma — and symmetrically, our existence statement does not formally deliver a
liminf-average equilibrium.

**Acceptance.** Our notion becomes interchangeable with the literature's in both
directions. This is where the Lean work would be if a valid counterexample ever
lands at these hypotheses.

### `LEAN-F0-4` — construct the infinite-play measure by Kolmogorov extension

- **Status:** READY
- **Lane:** F0
- **Depends:** `StochasticGame`, the finite-horizon `histDist` family,
  `LiminfAverageBridge`.
- **Record:** this file

**Objective.** **Foundations.** Construct the infinite-play measure for
`StochasticGame` by Kolmogorov extension, so the liminf-average bridge applies
without an assumed representation hypothesis.

**State.** `READY`. The two game-facing corollaries of the liminf bridge each
carry an explicit `hrep` hypothesis stating that a given process represents the
finite-horizon averages, because no infinite-play measure exists in the tree to
build it from. The finite-horizon `histDist` family is a coherent projective
family, so this is mathematically unproblematic — it is missing infrastructure,
not a further mathematical assumption, and it should be labelled as such
wherever it appears.

**Acceptance.** `hrep` disappears from the bridge's corollaries. Until then, no
statement depending on them may be described as unconditional.

### `LEAN-F0-5` — maintain the notion lattice and drive the F0 queue off it

- **Status:** ACTIVE
- **Lane:** F0
- **Depends:** The notions defined across `StochasticGame.lean`, `Uniform.lean`,
  and the quitting tree; the literature wing for what each is meant to match.
- **Record:** this file

**Objective.** **Foundations.** Maintain the notion lattice at
[`NotionLattice.md`](NotionLattice.md) and drive the `F0` queue off it: every
ordered pair of payoff/equilibrium notions is LANDED with a named theorem, OPEN
with a tracked row, FALSE with a counterexample, or N/A with a reason. No blank
cells, and ``standard'' is not an answer.

**State.** `ACTIVE`. The individual definitions were audited twice as faithful;
the failures are in the **relations between** notions, and every one found so
far was found by accident while proving something unrelated -- the missing
epsilon-notion at the `StochasticGame` level (which made `LEAN-F0-1` land
against a locally-invented predicate), the one-directional liminf bridge, and
the absent infinite-play measure. An implication believed because everyone knows
it is an OPEN cell, not a LANDED one.

**Acceptance.** Every gap between notions is a named row rather than a surprise.
A new notion may not be added without its node and edges recorded. **First pass,
2026-08-04:** 28 nodes in 8 clusters, ~40 edges — LANDED 19 (5 conditional on a
named extra hypothesis), OPEN 10, FALSE 4, N/A 6. Two structural absences it
exposed, both worth acting on independently: the repository has **no
continuation-aware Markov-perfect notion at all**, and
`StochasticGame.IsMarkovNash` — which occupies that name — checks only raw
`stagePayoff` against one-stage deviations, ignoring transitions and
continuations, and has **zero importers outside its own file**. It should be
renamed to what it is or removed. Separately, the liminf-average cluster
contains **no Lean `Prop`**: the literature's central payoff notion is reachable
here only through integrals in the bridge.

### `LEAN-F0-6` — package three implications used as self-evident

- **Status:** READY
- **Lane:** F0
- **Depends:** `Discounted.lean` and the Fink member lemmas; the
  monitored/repeated payoff-level notions;
  `isεHorizonNash_markovBehaviorProfile`.
- **Record:** [Notion lattice](NotionLattice.md)

**Objective.** **Foundations.** Package the three implications the notion
lattice found being used as if self-evident, with no theorem behind them.

**State.** `READY`, all three previously untracked. **(a)** A single discounted
Bellman equilibrium (Fink) implies a single-β discounted Nash equilibrium —
consumed piecewise across **37+ files** via member lemmas, never stated as one
theorem. **(b)** The converse of the monitored-repeated payoff-level equilibrium
to the fixed-profile notion — its own docstring flags that it needs a
compactness theorem, and nothing tracked it. **(c)** Stage-Nash implies
finite-horizon Nash only under the `IsActionIndependent` restriction; the
unrestricted case has no theorem and had no row.

**Acceptance.** Each is a named theorem or a named open row. An implication
consumed in 37 files is either proved once or recorded as an assumption — not
left implicit in the member lemmas that happen to discharge it.

### `LEAN-P1-1` — prove every two-player quitting game has stationary eps-equilibria

- **Status:** ACTIVE
- **Lane:** P1
- **Depends:** Full-rate cap, pair repair, source case split.
- **Record:** [Two-player
  theorem](../../ideas/TwoPlayerBaseCaseExhaustion/EveryTwoPlayerQuittingGameHasStationaryApproximateEquilibria.md)

**Objective.** Source-aligned six-scalar proof that every two-player quitting
game has stationary terminal epsilon equilibria.

**State.** `ACTIVE`; pure-case/orientation/vanishing-solo branch missing.

**Acceptance.** Target and umbrella build; terminal-to-uniform consumer; Q132
nonattainment regression.

### `LEAN-P1-2` — define stationary regret and its zero/positive gap dichotomy

- **Status:** READY
- **Lane:** P1
- **Depends:** `QuittingFullRateStationaryVerifier`.
- **Record:** [Stationary gap or
  escape](../../ideas/StationaryRepairExhaustion/StationaryExploitabilityHasGapOrEscapeDichotomy.md)

**Objective.** Define stationary regret and formalize zero-infimum/payoff versus
positive typed gap.

**State.** `READY`; packaging absent.

**Acceptance.** Exact dichotomy reaches terminal selection or negative search
API.

### `LEAN-P1-3` — package Q132's exact behavioral nonattainment table

- **Status:** PARTIAL
- **Lane:** P1
- **Depends:** behavioral hazards as quit-time/Never mixtures; stopping-law
  expectation identity.
- **Record:** [Nonattainment fence][naf]

**Objective.** Package Q132's exact behavioral nonattainment table.

**State.** `PARTIAL`. Scope corrected 2026-08-04: the table, the stationary
no-go, and the vanishing-error family are already production in
`QuittingTerminalPacketSimpleFallbackCounterexample.lean`; the actual gap is the
stationary-to-behavioral upgrade. Route settled — the stopping-law identity plus
a support-argmax lemma, **not** a non-stationary generalization of the
constant-root complementarity algebra. Draft in `experiments/` has the
infrastructure `sorry`-free and the degenerate case closed; one `sorry` remains
for reachability positivity and the finite per-atom case analysis.

**Acceptance.** Permanent regression for compactified cap/attainable-tail
claims.

### `LEAN-P1-4` — define the finite marked absorption-cylinder encoding and its identities

- **Status:** DESIGN
- **Lane:** P1
- **Depends:** Stable mathematical type from `MATH-P0-1`; existing finite
  exact-D and holonomy APIs.
- **Record:** [Enriched absorption paths][ep]

**Objective.** Define the finite marked absorption-cylinder encoding and prove
its exact payoff, obstacle/cap, debt, packet, anchor, and concatenation
identities.

**State.** `DESIGN` at **P0**: `PC-009` restored this lane, superseding
`PC-008`'s demotion; do not scaffold the infinite topology before the finite
semantic map is fixed.

**Acceptance.** Every production finite block embeds without changing its
strategic meaning; basis for P0 compactness and endpoint adapters.

### `LEAN-P0-2` — formalize the two carrier refutations that exist only as prose

- **Status:** ACTIVE
- **Lane:** P0
- **Depends:** Landed mismatch characterization.
- **Record:** [carrier group](../../ideas/AbsorbingCycleCarrier/README.md)

**Objective.** Formalize the two refutations that currently exist only as prose:
the two-coordinate weight refuting the disjunction, and the fences against the
blocking-digraph construction and against one-row convexity.

**State.** `ACTIVE`, in flight.

**Acceptance.** Permanent regressions; without them a future worker can restate
a refuted route.

### `LEAN-P0-5` — formalize that signed phasewise accumulation equals relaxed-cycle gain

- **Status:** READY
- **Lane:** P0
- **Depends:** `Math/CyclicMaxAffineBound.lean`, the companion-map machinery.
- **Record:** [signed
  accumulation](../../ideas/AbsorbingCycleCarrier/TheSignedAccumulationIsTheGain.md)

**Objective.** Formalize the identity that the **signed** phasewise accumulation
equals the gain of a relaxed cycle, and hence that its vanishing is necessary
and sufficient.

**State.** `READY`. The result is `M [reported]` and is the answer to the
conversion question, so it is the highest-value thing currently
believed-true-but-unformalized.

**Acceptance.** Makes the necessary-and-sufficient statement citable; the
envelope side is already landed.

### `LEAN-P0-6` — prove the pure quit-time supremum equals the companion map's fixed point

- **Status:** READY
- **Lane:** P0
- **Depends:** `QuittingRelaxedCycleGain`,
  `QuittingBehaviorPureTimeExtremality`'s pure-time reduction, the landed
  companion-map contraction.
- **Record:** [signed
  accumulation](../../ideas/AbsorbingCycleCarrier/TheSignedAccumulationIsTheGain.md)

**Objective.** Prove that the supremum over pure quit-time deviations of a
periodic root sequence equals the companion map's cyclic fixed point.

**State.** `READY`. The signed-accumulation identity is landed and is necessary
and sufficient **for the companion fixed point**. Identifying it with the
literal supremum over all behavioural deviations needs the pure-time reduction
(landed) composed with this optimal-stopping-equals-Bellman-fixed-point fact,
which is standard mathematics but appears nowhere in the tree. Until it lands,
`PC-009`'s ``the conversion is available'' is a statement about the fixed point,
not about deviations.

**Acceptance.** The gain identity becomes a statement about actual deviations,
closing the last step of the conversion.

### `LEAN-P2-1` — source-aligned FTV stationary-impossibility theorem

- **Status:** BLOCKED
- **Lane:** P2
- **Depends:** Recheck source epsilon quantifier.
- **Record:** [FTV literature result][ft]

**Objective.** Source-aligned FTV stationary-impossibility theorem.

**State.** `BLOCKED` on exact source statement.

**Acceptance.** Build-clean theorem reusing landed FTV table; positive cyclic
regression.

### `LEAN-P2-2` — discharge three prose-only items the model-faithfulness audit found

- **Status:** READY
- **Lane:** P2
- **Depends:** Two-player tables already in production.
- **Record:** [Model faithfulness audit](audits/2026-08-04-ModelFaithfulness.md)

**Objective.** Discharge the three prose-only load-bearing items the
model-faithfulness audit found.

**State.** `READY`. **(a)** Kuhn's theorem is **already formalized
generically**, and strictly *stronger* than the classical statement. Both
directions live at `GameTheory/Theorems/Kuhn.lean`. The strengthening is in
**M→B** — the direction that classically requires **perfect recall** — which
here is proved under **per-step recall** only (`PerStepActionRecall`: the joint
action is determined by the joint observation transition; `PerStepPlayerRecall`:
each player's action by its own), with a still weaker semantic version over
step/locality assumptions (`ObsModelCore.kuhn_mixed_to_behavioral_semantic`).
The audit's “unformalized WLOG” finding is wrong as stated; what is missing is a
stochastic/quitting-history **adapter** and verification of its hypotheses.
**Why the strength may matter here specifically:** perfect recall is free under
perfect monitoring, so it buys nothing for full-history strategies — but
`MarkovProfile` and stationary profiles carry *no* recall at all, and this
program reasons in those classes constantly. A per-step-recall Kuhn can apply
where the classical one cannot. **(b)** Two load-bearing non-redundancy claims
are prose arguments over concrete two-player tables and should be theorems,
since prose on a concrete table is exactly the shape that rots silently. The
audit also records a soundness argument worth preserving deliberately: the two
`sorry`-carrying modules are imported by nothing but each other and the root
aggregator, so no landed theorem can transitively depend on `sorryAx` — cheaper
and stronger than per-theorem axiom audits, but only while those modules stay
leaves.

**Acceptance.** Each item is a theorem or an explicitly scoped hypothesis; the
leaf property of the `sorry`-carrying modules is asserted somewhere a build can
check it, not left as an audit observation.

## Literature import lane

### `LIT-P1-1` — audit and formalize four-player fallback-collapse propositions

- **Status:** PARTIAL (inferred; source has no explicit status tag here)
- **Lane:** P1
- **Record:** [Four-player fallbacks
  fail](../../ideas/UniformEquilibriumLiterature/FourPlayerQuittingFallbacksFail.md)

**Objective.** Audit and formalize source-stable four-player fallback-collapse
propositions.

**State.** Primary final paper located; numerical period-two packet disputed.

**Acceptance.** Qualitative fences only, exact source attribution, no uncertain
constants.

### `LIT-P1-2` — complete the FTV source statement audit

- **Status:** READY (inferred; source has no explicit status tag here)
- **Lane:** P1
- **Record:** [FTV stationary fence][ft]

**Objective.** Complete FTV source statement audit.

**State.** Exact small-error quantifier needs reread.

**Acceptance.** Unlocks `LEAN-P2-1`.

### `LIT-P1-3` — audit the Solan-Solan Q-matrix normalization for a quitting preprocessor

- **Status:** PARTIAL (inferred; source has no explicit status tag here)
- **Lane:** P1
- **Record:** [Non-Q quitting games][nq]

**Objective.** Audit the Solan--Solan Q-matrix normalization and import the
non-Q ordinary-uniform theorem as a quitting preprocessor.

**State.** Preprint full text audited 2026-08-03: matrix/LCP/`Q` conventions
resolved. Two scope corrections landed — the non-`Q` conclusion is a synthesis
of Lemma 2.6, Lemma 2.10, and Theorem 2.11(1), and is stated
stationary/undiscounted, not uniform. Residual blocker is the Solan--Vieille
uniform upgrade.

**Acceptance.** Classify tables and test whether the positive-debt residual
necessarily lies on the still-hard Q side.

### `LIT-P2-1` — define the positive-recursive nonrectangular theorem's repository adapter

- **Status:** READY (inferred; source has no explicit status tag here)
- **Lane:** P2
- **Record:** [2025 result][pr]

**Objective.** Define the positive-recursive nonrectangular theorem's exact
repository adapter.

**State.** Recorded, no consumer/interface.

**Acceptance.** Check examples and expose construction data useful to boundary
repair.

### `LIT-P2-2` — separate Bewley-Kohlberg inputs from the independent Puiseux route

- **Status:** READY (inferred; source has no explicit status tag here)
- **Lane:** P2
- **Record:** [MN/BK
  result](../../ideas/UniformEquilibriumLiterature/MertensNeymanDependsOnBewleyKohlbergSelection.md)

**Objective.** Separate source-aligned Bewley--Kohlberg inputs from the
independent Puiseux route.

**State.** Singular general Shapley branch and source proof audit.

**Acceptance.** No unconditional classical theorem claim until selection,
variation, and limit identification are explicit.

### `LIT-P1-4` — second round of reference-chain closure and flagged-item intake

- **Status:** ACTIVE (inferred; source has no explicit status tag here)
- **Lane:** P1
- **Record:** [Reference-chain closure
  audit](audits/2026-08-04-ReferenceChainClosure.md)

**Objective.** Second round of reference-chain closure, and intake of the top
flagged items.

**State.** Round one closed **10 of 25** source papers (258 references across 13
lists) and flagged **34** unrecorded works. The 15 unclosed are mostly
recoverable — arXiv ids already identified, the sweep stopped on API rate
limits, not on unavailability. Highest-value flags: AGKRS's own 2026 sequel *The
APS approach for undiscounted quitting games* (IJGT 55(1), same four authors,
apparently the publication of AGKRS 2022's own "in preparation" reference);
Simon 2007 *The Structure of Non-Zero-Sum Stochastic Games*, cited independently
by 7 of the 13 closed lists and already half-known to the wing as "not located";
and Neyman's *Real Algebraic Tools in Stochastic Games*, which speaks directly
to the repository's own recorded Tarski--Seidenberg gap.

**Acceptance.** Closure above 80% of the scoped set, wing records for the
flagged items judged load-bearing, and an explicit statement of what remains
unread. Topic-vocabulary search is not an acceptable substitute: it returned NOT
LOCATABLE twice on a citation that was exact. **Sweep the repository's own
unprocessed PDFs as part of this.** Twice in one session a decisive source was
already on disk and unread: the withdrawn Simon preprint, and Solan's PhD
dissertation at `ephemeral/old/_source_eilons_thesis.pdf`, whose Section 4 is
the refereed MOR material and which settled the largest borrowed-premise
exposure in the tree. Note also that `ephemeral/sources/aps-quitting-2026.pdf`
is a 3 KB HTML bot-block page, not a paper.

### `LIT-P2-3` — close the three residues of the borrowed-premise census

- **Status:** READY (inferred; source has no explicit status tag here)
- **Lane:** P2
- **Record:** [Borrowed-premise
  census](audits/2026-08-04-BorrowedPremiseCensus.md)

**Objective.** Close the three residues of the borrowed-premise census that
citation edits could not.

**State.** Three items, each verified as genuinely open rather than assumed.
**(a)** Two consumed results have **no wing record at all**: Solan--Vieille
(2001) Prop. 2.13, cited ~15 times across the tree, and
Ashkenazi-Golan--Krasikov--Rainer--Solan, *The APS Approach for Undiscounted
Quitting Games*, IJGT (2026). **(b)** Solan--Solan 2020's scope corrections are
keyed to **preprint** numbering (2.6, 2.10, 2.11); the published MOR version was
never retrieved and nothing in the repository pins it, so if MOR renumbered,
downstream discharge obligations point at the wrong results. **(c)** The census
asserts a mis-pairing at
`QuittingGameConjecture/BackgroundAndDerivations.md:488-496`, footnoting the
Solan--Solan sunspot claim to the LCP paper; a second reader could not confirm
it, since the LCP paper itself states its Theorem 2.4 is its main result and
that is the claim cited. Adjudicate rather than silently "fix".

**Acceptance.** Wing records for the two unrecorded results; the MOR numbering
pinned or the preprint dependence made explicit at every discharge site; a
verdict on (c) recorded in the census.

## Engineering and documentation lane

### `ENG-P0-1` — put CI under .github/workflows/ and make it green

- **Status:** READY (inferred; source has no explicit status tag here)
- **Lane:** P0

**Objective.** Put CI under `.github/workflows/` and make its documented
commands green.

**State.** Current `.github/ci.yml` is not discovered; placeholder and
repository audits fail.

**Acceptance.** A clean clone runs build, placeholders, repository audit, and
axiom audit deterministically.

### `ENG-P0-2` — make the axiom audit exact and add P0 keeper capstones

- **Status:** READY (inferred; source has no explicit status tag here)
- **Lane:** P0

**Objective.** Make axiom audit exact and add P0 keeper capstones.

**State.** Multiline parser misses 10/48 outputs; prerequisite build implicit.

**Acceptance.** Requested declarations equal parsed declarations; explicit build
target; quitting/uniform keepers audited.

### `ENG-P0-3` — run integration-sweep after every parallel-work wave, before committing

- **Status:** ACTIVE (inferred; source has no explicit status tag here)
- **Lane:** P0

**Objective.** Run the `integration-sweep` agent after every wave of parallel
work, before committing.

**State.** Parallel agents each see only their own slice, so the join is where
drift accumulates: statuses superseded by a later decision but still citing the
earlier one, Lean that landed without its owning claim file or `FRONTIER.md`
saying so, prose asserting something is open after it has been answered,
citations corrected in the prose but not in the Lean docstrings, and
question-numbering collisions between concurrent sessions. Every one of these
occurred in a single session.

**Acceptance.** Definition at `.claude/agents/integration-sweep.md`. It fixes
only what has exactly one correct answer and reports judgment calls unfixed; its
stop-and-report case is the leaf invariant — if a `sorry`-carrying module
acquires an importer, the repository's whole `sorryAx`-freedom argument lapses.

### `ENG-P1-1` — classify the 25 root-unreachable Lean modules and opaque/native_decide policy

- **Status:** READY (inferred; source has no explicit status tag here)
- **Lane:** P1

**Objective.** Classify 25 root-unreachable Lean modules and
`opaque/native_decide` policy.

**State.** Stable library, regression, certificate, and research surfaces
currently mixed.

**Acceptance.** Every module has an intentional target/import surface; policy
exceptions are explicit.

### `ENG-P1-2` — keep the pipeline/frontier and claim-level links clean and current

- **Status:** ACTIVE (inferred; source has no explicit status tag here)
- **Lane:** P1

**Objective.** Keep this pipeline/frontier and claim-level venue link-clean and
current.

**State.** Migration in progress; ignored intake has stale links.

**Acceptance.** Cold-handoff check passes; no durable status depends only on
ignored files.

## Dependency and gate view

```text
terminal approximate existence <=> uniform payoff                         [L]
                ^
                |
zero optimized debt ---------------------------------------------------- [L]
                |
positive plateau -> anchored packet + two endpoint charts -------------- [L]
                |
actual finite middle -> compositional boundary holonomy ---------------- [L]
                |
fixed-cutoff resolved lift compact/closed; literal length fence -------- [L]
                |
       MATH-P0-1: tightness OR infinity chart + bounded decoder
                     OR calibrated incompatibility
                |
       MATH-P0-2: anchored repair (zero-pinned grammar); fixed root-debt
                    descent is closed -- see
                    ideas/PositivePlateauBoundaryClosure/
                    AnchoredRepairOrUniformDebtDescent.md
                |
terminal approximate existence
```

`MATH-P0-3` can bypass part of the bridge by finding a short repair. The
refutation lane is logically independent after the terminal/nonexistence waist.
Two-player formalization, literature imports, and engineering work are safe
parallel lanes; none should be described as closing the P0 hinge.

## Milestones that changed this queue

- Terminal-to-uniform quitting uniformization and fixed-payoff selection moved
  the hard problem entirely to terminal existence.
- Arbitrary behavioral quitting deviations became mixtures of deterministic quit
  times and Never, closing a major strategy-class interface.
- Full-rate stationary caps became exact for arbitrary stationary products.
- `e2d5170` landed two-ended exact-D compactification and the reverse terminal
  packet; the missing object became the middle, not the point at infinity.
- `e1fe7dc` landed exact finite-chain `QuittingBoundaryHolonomy`; finite-block
  algebra is no longer open. Arbitrary-length executability and strategic
  decoding remained open.
- `14d75ff` proved that the full fixed-cutoff provenance lift is compact and
  closed, and that any compact lift retaining a literal natural-valued length
  coordinate has uniformly bounded length. The open object is therefore an
  escaping-length tightness/decoder theorem, not fixed-word topology.
- Uniform middle-length tightness was refuted by an explicit two-player weight
  with optimized debt `1/8` at every cutoff and all mass escaping to a receding
  terminal row (`PC-003`); bounded exact-extension descent was then refuted as a
  cutoff-independent root-debt decrement (`972ba5e`); and both known
  positive-debt plateaus were shown to be manufactured by pinning the terminal
  continuation to zero -- both witnesses are two-player tables with exact
  zero-debt equilibria once unpinned, and both equilibria are machine-checked
  (`3b04928`).

## Handoff maintenance

Before handoff, update the audited commit, uncommitted-work warning, active
blockers, and any PC decision changed by new evidence. A theorem/refutation
commit updates its exact claim file; a changed mathematical boundary also
updates `FRONTIER.md` in the same stable point or an immediately following doc
commit. A priority/route change gets a PC row here. Formalized status requires
an exact declaration/path and successful check; published status requires source
attribution and a scope adapter.

## Link references

A few `../../ideas/...` destinations below are long enough that even the bare
path approaches or exceeds 100 columns; the tags below keep every inline use
short, at the cost of these definition lines, some of which still exceed 100
columns -- that residual is the path length itself, not a wrapping choice.

[anchored-repair]: ../../ideas/PositivePlateauBoundaryClosure/AnchoredRepairOrUniformDebtDescent.md
[ep]: ../../ideas/PositivePlateauBoundaryClosure/EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md
[gbp]: ../../ideas/VanishingDiscountResponseSynthesis/DiscountedCertificatesConvergeToGainBiasPackets.md
[welf]: ../../ideas/PositiveWelfareSeparator/FailedRepairMayYieldPositiveGlobalWelfareSeparator.md
[cex]: ../../ideas/QuittingGameConjecture/CounterexampleNeedsPositiveBehavioralExploitabilityGap.md
[naf]: ../../ideas/StationaryRepairExhaustion/NaiveStationaryCompactificationNeedNotAttainEquilibrium.md
[ft]: ../../ideas/UniformEquilibriumLiterature/FTVCyclicGameHasNoStationaryApproximateEquilibria.md
[nq]: ../../ideas/UniformEquilibriumLiterature/NonQQuittingGamesHaveUniformApproximateEquilibria.md
[pr]: ../../ideas/UniformEquilibriumLiterature/PositiveRecursiveNonrectangularGamesHaveUniformPayoffs.md
