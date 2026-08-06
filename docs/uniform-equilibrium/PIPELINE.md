# Uniform-equilibrium project pipeline

**Production-Lean checkpoint:** `5e7d0e7a`.  The last complete repository
audit remains the 2026-08-03 pair `14d75ff` / `cd1db11`. **This file revised
2026-08-07** — discrete hazard stopping laws, finite phase-occupation duality,
target-anchored payoff closure, and conditional multi-owner face-circulation
uniform-payoff compilation are incorporated and reflected below.

This is project-control truth: decisions, dependency priorities, gates, and
acceptance conditions. It is not a mathematical exposition. The fixed-cutoff
holonomy compactness work is committed and counted; the marked absorption-path
route is a selected open design, not production mathematics. New Lean files are
never counted as landed until committed, built, and reflected in the owning
claim and [`FRONTIER.md`](FRONTIER.md).

**Handoff validation.** At the last fully audited checkpoint, `lake build`
succeeded, local Markdown links resolved, and the repository audit exited
zero.  For the 2026-08-06 incorporation, targeted builds of
`UniformPayoffExistenceClosure`, `QuittingEssentialAPSInfiniteContraction`, and
`QuittingSupportWitnessUniform` completed without warnings; the generic cyclic
exposure module and its two direct consumers also checked cleanly. The
subsequent `QuittingEssentialAPSUniformPayoff` and public
`QuittingEssentialAPSAll` dependency closures likewise built without warnings.
A full root build and audit were deliberately not repeated: this lane optimizes
fast experimentation with dependency-closure confidence rather than a complete
audit on every mathematical commit.  The previous audit established zero orphans,
the restored axiom audit reporting only `propext`, `Classical.choice`, and
`Quot.sound`, and the leaf invariant checked by the script. The `opaque` and
`native_decide` occurrences survive only inside the quarantined `BlockPairK11`
island, reported as accepted exceptions whose exemption is **earned** by a
containment check that fails the audit if anything imports the island. The three
intentional `sorry` declarations are
`exists_uniformDeviationCapConstructor` in `UniformExistenceConjecture.lean` and
`quittingGame_exists_uniformEquilibriumPayoff` in `QuittingConjecture.lean`,
and the reduced cap-package leaf in `QuittingReducedCapConjecture.lean`.
These are owned by the engineering queue below and the [proof-engineering
audit](../../ephemeral/ProofEngineeringAudit.md), rather than blockers hidden in
the P0 mathematical status.

## Incorporation checkpoint — 2026-08-07

- **Uniform consequences (`c81bcba8`, production).** Profile-uniform vanishing
  finite-average payoff gaps preserve each exact target; bounded expected
  potential shaping supplies the endpoint-telescope instance. Tail width and
  excess work are exact reverse diagnostics, while rare transitions rule out
  unrestricted kernel-continuity transfer. None is a general-game producer.
- **Face circulations (`5e7d0e7a`, production).** A supplied bounded
  `FaceCirculationCertificate` with a common phase-ratio ceiling below `1` and
  floor at least `quittingPunishmentValue` is a genuine quitting-game producer:
  balanced multi-owner circulation, compact reversal to a chronological
  support path, joint-survival selection, and the uniform-payoff compiler yield
  an existential payoff. The theorem neither constructs certificates for
  arbitrary games nor identifies the selected payoff with a named certificate
  vertex. The scaled cyclic and repaired four-player stress weights are concrete
  corollaries.
- **Closure and duality interfaces (`a405f8a6`, `1773ce7e`, `94160ee5`,
  production).** Generic discrete-hazard stopping laws now underlie the
  quitting adapters. Target-anchored tails, parametric residue payoffs, and
  reward-limit closure consolidate the payoff consumer. Finite phase-occupation
  LP/duality proves semantic strong duality only conditional on a supplied
  phase occupation; it does not establish occupation nonemptiness or act as a
  strategic producer.

- **Generic cyclic exposure (`a0ab77aa`, production).**  The sharp
  `min exposure <= 1/4` theorem and fair-row rigidity now hold for every finite
  permutation system.  The three-player shared-punishment result is a direct
  specialization; duplicated three-coordinate case algebra was removed.
- **Reward perturbation and target-free closure (`eceee7bb`, `b0eee54a`,
  production).**  A uniform reward perturbation of size `rho` moves every
  prescribed or deviating finite-horizon payoff by at most `rho` and transfers
  Nash error by `2 rho`.  Mere existence is closed under uniform reward-table
  limits on a fixed finite skeleton: nearby targets are bounded in a common
  payoff cube, and only a target subsequence is compactified.  Therefore dense
  coverage by solved reward tables would prove full fixed-skeleton coverage.
  No density theorem for the current mechanism catalog is claimed.
- **Essential APS (`b702f477`, conditional positive stratum).**  Compact
  functional unique-live fibers admit coherent infinite execution, uniform
  shifted-window mass, opponent-mass charging, exact Bellman transport, and a
  common opponent-survival block contraction. Compact terminal-freeness also
  gives a uniform coarse-hazard ceiling. Fixed logarithmic subdivision makes
  the local Quit error vanish without changing coarse survival, and a
  nonperiodic Snell supersolution compiles every initial point in the component
  to a uniform-equilibrium payoff. The theorem does not prove that this
  component exists or covers the relevant payoff set in arbitrary games.
- **Support witnesses (`a4f23756`, conditional compiler).**  Retaining the
  support-local endpoint witness collapses the ledger clock deterministically.
  Divergent support-rational paths compile with error
  `2 delta + r + sqrt(delta) (2 + 7 M)`; finite cycles with one absorbing phase
  adapt to the same compiler.  Existence of such paths/cycles at every
  tolerance remains the producer obligation.  The abstract rank-one crossing
  theorem is retained separately and supplies no game-specific process or
  variation bound.

The resulting priority delta is precise: test density of the positively solved
payoff-table strata first; independently seek a support-rational path/cycle
producer; and, on the APS lane, determine when an arbitrary game supplies a
nonempty compact terminal-free unique-live component with the required face
avoidance. None of these conditional compilers receives generic existence
credit before its producer is proved.

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

## Priority stack (2026-08-05, post-review reordering)

Adopted after four independent reviews of the position summary
(`ephemeral/ReviewOfSummary.md`); the review acceptance is binding until a
result changes it. The order is by decisiveness, not by ease:

1. **Compiler assembly — CORE DONE** (`QuittingBoundedWindowLanding`,
   `QuittingTruncationLedgerFold`, `QuittingReducedCapConjecture`). The
   landing consumes the bounded predicate directly and composes with WCM
   into a zero-granted-predicate chain; the fold lives at the value level
   (raw-ledger folding proved **false** — the truncation correction
   telescopes to order one at rarely-reached stages; constant `5B·reach`);
   and **the reduced conjecture exists as the third intentional leaf**:
   `HasQuittingLedgerCapPackage`, six arithmetic clauses, with
   package ⟹ conjecture proved gap-free. The program's progress metric is
   now clause shrinkage. Mathematical residue, named: clause (iv) at the
   punished player and in Case 1 (awaits the excursion layer); clause (v)
   below the solo-clipped ceiling (punishment attainment — Q162's band);
   package *production* (the engines). **Of the two paper IOUs the
   equivalence's outer legs lean on, the stationary min-max formula LANDED
   2026-08-05** (production `0829959`, `QuittingStationaryMinMax.lean`):
   `χ = inf_y Φ(y)` with BOTH legs machine-checked in full
   history-dependent generality, no attainment asserted;
   `quittingRootSequenceHazardTerminalValue_const_le_cap` supplies the
   phase-switch hypothesis (P) with `punishCap = Φ(y)` for ANY constant
   row — strictly below the solo-clipped ceiling whenever
   `inf Φ < max(solo, 0)`, witnessed by `QuittingProfitableSoloTwoCoordinate`
   (χ = 0 vs ceiling 2). Clause (v)'s "below the solo-clipped ceiling"
   residue is therefore now reachable machinery, not an IOU. Still owed:
   the Solan–Vieille perfection-to-equilibrium proposition (SV-2.6), and
   the bridge `lim_T punishmentLevel = quittingPunishmentValue` (inf/sup
   vs limit uniformity — noted, unclaimed). **The clause (P) attack:
   design complete, formalization NOT started** (the dispatched agent
   stopped at the design phase; full hand-verified design recorded at
   `ephemeral/ClausePAttackDesign.md`). Established there: per-player
   attainment at `χ + η` is a 4-line route; the opponents-congruence
   lemma is ≈ rfl and glues a TWO-PLAYER simultaneous clause-(P)
   discharge at exact χ (under `Fintype.card ι = 2`, replacing the
   solo-ceiling discharge; remaining two-player clauses L/Q/R/A); and a
   hand-verified cyclic `Fin 3` table SEPARATES simultaneous from
   per-player punishment — every shared plan leaves some player at
   `χ + 3/4` (AM–GM at row zero; Lean-cheap). Flagged discovery, not
   proved: on the absorption-branch variant, simultaneous punishment is
   the Steinhaus–Trybuła non-transitive-dice problem and time-varying
   plans plausibly BEAT stationary ones — the stationarity theorem
   plausibly fails for simultaneous punishment; POSED as **Question 168**
   (2026-08-06): the exact 3/4 separation, the dice-table stationarity
   verdict with the full stopping-reply supremum, attainment and bounds,
   and the shared-versus-triggered pricing.
   Next session: dispatch the module from the recorded design. **INTAKE PENDING (2026-08-05,
   answer arrived, snapshot-committed `9baa177`, NOT yet sealed): the
   Q163 answer** — verdict headline: the equivalence's hard direction
   repairs WITHOUT support purification; the weighted correspondence
   yields exactly the WCM inequality the landing consumes (∃ρ > 0:
   ρ-rational + weighted-ρ-near ⟹ c(x) ≥ ρ, by separation from the
   c = 0 face using only absence of instant approximate equilibria) —
   discharging its K4 directly; global support purification is FALSE
   (rowwise thresholding fine, but global ε-equilibria exist whose
   every nearby support-perfect plan has order-one exploitability); the
   published lemma's weighted reading is false, its support-perfect
   reading repaired via the Solan–Vieille perfection-to-equilibrium
   proposition — RAISING SV-2.6's priority (it now gates both an outer
   leg and this repair). Next session: full read of the 819-line
   answer, seal in ideas/, then formalize the WCM inequality.
1a. **The χ-floored certificate re-measurement — DONE, verdict split and
   decisive** (`QuittingCirculationChiFloorBoundary.lean`). Solo-rate and
   pair-repair **fall** to the χ-floored free-hazard variant (the previous
   boundary's own witnesses are inside it; the sub-solo blind spot was a
   floor artifact — and the premise correction: multi-owner phases supply
   no simultaneous collision mass, the deterrent is the owner's own
   hazard). Zero-solo and joint-exit **survive structurally**: their
   payoffs provably leave the solo-row hull, which every circulation
   target inhabits — no floor can fix a range restriction. **The habitat
   moves**: weights whose equilibria pay outside the solo hull with no
   exact mechanism. **The engine extension is named**: circulations
   through arbitrary coalition faces, per-phase condition = the
   sure-exit-set criterion — which is exactly Q165's Part B object, so
   the `n = 3` test and the engine extension are now one road.
2. **`n = 3` through the architecture — Q165 ANSWERED 2026-08-05, verdict:
   inexpressibility, with the missing producer named** (sealed in
   `ideas/TheBranchGateNeedsTwoBlockersAndSwitchRepair.md`). Single-blocker
   designation is **false** (uniform-obstruction counterexample); the sharp
   gate is two-blocker (universal ∨ switching pair) at every `n`. The
   sure-exit-set theorem holds exactly as posed (= the coalition-face
   per-phase condition from 1a — that road is confirmed). Collision
   compensation survives a third party only under three exact scalar
   conditions (owner indifference at interior rate; punishment-independent
   spectator no-join; blocker-floor balance against the **exact** χ);
   the fixed-gap obstruction kills sub-floor compensation at vanishing
   owner rate — `δ ≥ γ/(γ+p)` is forced. The fixed-blocker branch map is
   **not total**: a rational regression (C.20) escapes every branch; the
   missing constructor is `SwitchRepair : two-blocker rate cover ⟶
   two-scale rational relaxed orbit` (interior collision intensity within
   phases, occupation charge λ↓0 across them) — circulation is its
   compiler, not its producer; graded pinning cannot substitute. Successor
   items: (a) Theorems A/B + the C.20 regression **LANDED 2026-08-05**
   (production `97b77b6`: `QuittingBlockerIntervalCover`,
   `QuittingSureExitSet`, `QuittingSwitchingResidueRegression`; root
   build green, axiom audit clean; bonus: "exactly one" refuted, n = 2
   threshold corollary); (b) Theorem C equivalence **LANDED 2026-08-05**
   (production `34fdc11`, `QuittingCollisionRepairCharacterization.lean`:
   full iff against the exact χ, both legs, general `n`, forced-rate and
   sub-floor-failure corollaries, rate-1 collapse to the sure-exit test);
   (c) `SwitchRepair` — **Q166 ANSWERED 2026-08-05, verdict: REFUTED as
   posed** (sealed in
   `ideas/TheMissingOperationIsSupportEnlargementNotASecondScale.md`).
   The no-resurrection theorem: the occupation charge occurs in none of
   the packet's pointwise clauses, so vanishing-error two-scale families
   of sure-blocker packets (rates bounded below) exist iff an exact
   one-stage repair or sure-pair set already does — occupation scaling
   cannot repair a pointwise inequality, and rotating owners does not
   average failure away. The K4 regression was never in the residue: it
   has an exact rational period-one orbit (`x* = (1, 2/7, 1)`,
   `v* = (5/7, 0, 2/7)`, quit mass 1, Bellman trivial) absorbed by the
   existing exact-cycle engine, exact floors `χ = (2/3, 0, 2/7)` with NO
   sub-floor gap anywhere, and uniform packet defect 2/5 — the
   obstruction lives at the branch interface, not in the orbit relation.
   The missing operation is **support enlargement**: Theorem C.1, the
   one-sure-blocker/two-owner root (both non-blockers mix at explicit
   rational indifference rates; blocker quit-now inequality; floors) is
   necessary AND sufficient for an exact stationary terminal equilibrium
   on that cell — on K4 it recovers the second exact root
   `(1/2, 1, 1/3)`. Residues exactly characterized and semialgebraic:
   packet residues (switching/universal) ∩ no-two-owner-root =
   `ℜ₃^local`, which longer cycles/circulation may still absorb but
   blocker-cover data alone cannot decide. Successor items: (c1)
   formalize Theorem C.1 + the no-resurrection corollary layer on the
   landed collision-repair module + the K4 exact checks (χ against
   `quittingPunishmentValue`, the period-one root, the 2/5 defect) —
   unblocked, NOT yet dispatched (session stopping point); (c2) the
   `ℜ₃^local` adjudication is POSED as **Question 167** (2026-08-06):
   emptiness of the locally-blocked class or a member plus engine
   adjudication — either outcome a coverage theorem;
   (d) four-player delta: unchanged and explicitly untouched by Q166
   (the packet theorem has one spectator, the two-owner root none
   inactive; the two-spectator common-punishment obligation stands).
3. **The corrected trap schema — Q164 ANSWERED 2026-08-05, verdict: sound
   and semantically complete, but effectively sufficient-only** (sealed in
   `ideas/BoundedOrbitBudgetsAreExactlyBoundedPotentials.md`). The schema
   is sound by telescoping (consequence via repaired Simon (i)⇒(iii)
   contrapositively only — the ε/5 bookkeeping is irrelevant), and the
   format is **complete**: uniform finite-orbit quit mass bounded ⟺ a
   bounded local potential exists (budget-to-go V; exact strong duality
   B* = min osc Φ, no compactness or attainment). But no decision
   procedure: affine and every fixed semialgebraic template are exactly
   decidable by QE (affine has the convex-separation criterion with a
   finite Carathéodory dual on failure); continuous classes are provably
   incomplete (discontinuities at zero-charge accumulation strata can be
   necessary); the completeness⟹decidability hope is false absent an
   effective regularity theorem. Negative filters before synthesis:
   positive-charge fixed edge/cycle (kills all classes; the quit-bonus
   table's exact q=1/2 self-loop is the mandatory negative control),
   zero-drift-in-hull (affine). Successor items: (a) + (b) **LANDED
   2026-08-05** (production `0829959`: `Math/ChargedPathBudget.lean` +
   `ChargedPathBudgetCounterexamples.lean` — the abstract theorem, exact
   strong duality attained by the budget-to-go, Bellman
   least-supersolution characterization, positive-cycle filter, towers,
   the continuous-incompleteness counterexample FULLY proved, and the
   quit-bonus q = 1/2 self-loop calibration; the wiring to the repo's
   `oneStageNext` operator TAKEN same day, production `34fdc11`,
   `QuittingQuitBonusSelfLoopBridge.lean` — the canonical operator on the
   repo's own table fixes the calibrating value exactly, no bounded
   potential); (c) the QE/CAD search instrument itself is
   experiments-lane work, gated on nothing.
4. **Directed search in the named habitat** (sub-solo compensation at every
   owner), instrumented per 3, with the perimeter weights as mandatory
   negative controls.
5. **Strata geometry as the long bet — gated**: the route is not
   well-posed until a uniform-across-periods structure exists (the union of
   strata over unbounded periods need not be tame); the three-lens
   identification is demoted to working hypothesis (one leg proved) and is
   this route's first milestone, not its foundation.

**Conditional essential-APS singleton-flow interface — LANDED.** The exact
Flesch successor graph, full-convex-hull algebraic operator, executable segment
subrelation, carrier-restricted greatest fixed family, and zero-mass regression
are formalized. A supplied finite proper cycle embeds in the algebraic family
and compiles to a uniform-equilibrium payoff. More generally, compact
functional unique-live terminal-free fibers with finite-window face avoidance
produce a coherent infinite path, uniform opponent contraction, and a hazard
ceiling below one. Fixed subdivision and the nonperiodic supersolution then
prove that every initial point in that component is a uniform-equilibrium
payoff. The remaining APS obligation is structural coverage: no theorem shows
that every quitting game has such a nonempty component. See
[`EssentialAPS.md`](EssentialAPS.md).

Standing corrections from the same review acceptance: the negative map's
completeness claim is scoped (proofs factoring through our interfaces; the
correlated/de-correlation route and the topological route are unfenced);
"sound end to end" means locally machine-checked joints, not one assembled
theorem, until 1 closes; the public statement of the position lives at
`GameTheory/Concepts/Stochastic/UniformEquilibriumProblem.md` and is the
external attack surface.

## Status index

One line per item, grouped by work-cycle stage so what is ready, moving,
stalled, and finished is visible at a glance. Within a group, items are listed
lane by lane (`MATH`, `NEG`, `LEAN-F0`, `LEAN-P*`, `GEN`, `LIT`, `ENG`), then
by number, not in file order. Every status word carried by any `###`-headed
row below has a home in exactly one of the four buckets. `PC-*`
project-control decisions are not work items and are tracked by the
[Project-control decisions](#project-control-decisions) section itself; the
one decision that carries its own `Status:` field (`PC-010`, `RESOLVED`) is
cross-listed under `DONE / SOLVED / RESOLVED` for that reason alone.

**READY / PLANNED / DESIGN** — pick up now
- `MATH-P0-5` — is the exact-cycle disjunct complete, or do ε-cycles diverge?
- `MATH-P0-6` — port the all-periods non-existence theorem
- `MATH-P0-7` — a sufficiency theorem for the isolated-negative branch
- `MATH-P0-8` — the relaxed compiler: formalize Proposition 3
- `MATH-P0-10` — the drift device: uniform threats against moving states
- `MATH-P1-1` — re-derive Q148's encoding into the isolated-negative branch
- `MATH-P1-2` — test affine hazard domination on the exact-D families
- `MATH-P1-4` — formalize the weight whose gap survives faithful unpinning
- `MATH-P1-5` — audit the decomposition for instant approximate equilibria
- `NEG-P0-2` — the orbit-side counterexample criterion
- `LEAN-F0-1` — formalize the state-dependent-to-independent action-set padding
  reduction
- `LEAN-F0-2` — make the absorption fence structural, closing the all-continue
  vacuity trap
- `LEAN-F0-3` — bridge finite-horizon average to the liminf-average game
- `LEAN-F0-4` — construct the infinite-play measure by Kolmogorov extension
- `LEAN-F0-6` — package three implications used as self-evident
- `LEAN-F0-8` — the bounded-transversality lemma behind the case-2 repair
- `LEAN-P0-5` — formalize that signed phasewise accumulation equals
  relaxed-cycle gain
- `LEAN-P0-6` — prove the pure quit-time supremum equals the companion map's
  fixed point
- `LEAN-P0-7` — two-clock punishment for the deviation-cap constructor
- `LEAN-P1-1` — the n≥3 blocker-designation lemma (retargeted; n=2 closed
  separately by the capstone)
- `LEAN-P1-2` — define stationary regret and its zero/positive gap dichotomy
- `LEAN-P1-4` — define the finite marked absorption-cylinder encoding and its
  identities (`DESIGN`)
- `LEAN-P2-2` — discharge three prose-only items the model-faithfulness audit
  found
- `GEN-P1-1` — the positive-recursive program (V5), scoped (`PLANNED`)
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
- `ENG-P1-3` — dependency drift, and an over-specific upstream lemma

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
- `LEAN-F0-9` — name the recurring mechanisms as objects
- `LEAN-P0-2` — formalize the two carrier refutations that exist only as prose
- `LEAN-P0-9` — machine-check the weight with relaxed cycles at every tolerance
  and no exact one (`IN FLIGHT`)
- `LIT-P1-4` — second round of reference-chain closure and flagged-item intake
- `ENG-P0-3` — run integration-sweep after every parallel-work wave, before
  committing
- `ENG-P1-2` — keep the pipeline/frontier and claim-level links clean and
  current

**PARTIAL / BLOCKED / PENDING / ANSWERED IN PART**
- `MATH-P0-4` — map AGKRS Theorem 3.4 clause by clause against the internal
  trichotomy
- `MATH-P0-9` — the lock/unlock dichotomy for orbit variation (`ANSWERED IN
  PART`) — the open core, reshaped
- `MATH-P1-3` — decide whether quitting is complete for the general
  conjecture (`BLOCKED`)
- `MATH-P2-2` — derive a positive global welfare separator, or refute the
  lift (`PENDING`)
- `MATH-P2-3` — route an analytic Bellman/value leaf through a strategic gate
  or obstruction (`PENDING`)
- `MATH-P2-5` — give exact-D anchors a digraph structure and test bounded
  loop erasure (`PENDING`)
- `LEAN-P1-3` — package Q132's exact behavioral nonattainment table
- `LEAN-P2-1` — source-aligned FTV stationary-impossibility theorem
  (`BLOCKED`)
- `LIT-P1-1` — audit and formalize four-player fallback-collapse propositions
- `LIT-P1-3` — audit the Solan-Solan Q-matrix normalization for a quitting
  preprocessor

**DONE / SOLVED / RESOLVED**
- `LEAN-P0-1` — landed debt-transport, cycle-mismatch, FTV, and germ-bridge
  results this cycle — see [archive](PIPELINE-Archive.md)
- `LEAN-P0-3` — pin the matching scaling case in the germ bridge — see
  [archive](PIPELINE-Archive.md)
- `LEAN-P0-4` — discharge nondegeneracy of the germ quit family — see
  [archive](PIPELINE-Archive.md)
- `LEAN-F0-7` — the tail-average transfer is mirrored, not doubled —
  **to archive**
- `LEAN-P0-8` — joint complementarity, and absorption derived rather than
  assumed — **to archive**
- `LEAN-P0-10` — separate the three contraction deficits and price
  re-closing — **to archive**
- `LEAN-P0-11` — bridge the two encodings of complementarity — **to archive**
- `LEAN-P1-5` — linear complementarity infrastructure — **to archive**
- `MATH-P0-11` — the minimal open family: the four-player cyclic phase
  diagram (`SOLVED`) — **to archive**
- `PC-010` — PC-009's stated basis is established, at the bounded form
  (`RESOLVED`); a project-control decision, cross-listed here only because it
  carries a `Status` field, not an archive-rule item

**To archive.** Six rows above carry a finished status but still have a live
`###` section, in violation of "finished items move to
[`PIPELINE-Archive.md`](PIPELINE-Archive.md) exactly once": `LEAN-F0-7`,
`LEAN-P0-8`, `LEAN-P0-10`, `LEAN-P0-11`, `LEAN-P1-5`, `MATH-P0-11`. Noted here
rather than moved — moving sections is a separate pass.

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
where boundedness enters unstated, so the bounded form is mathematically
established (the gap is a missing step in a published proof, not a wrong
result) — and the bounded form is what the finite-cycle deduction needs,
since repeating a cycle lands inside that hull. The case-2 row returns to
`PROVED` **at the math level**: `NoBoundedCompletelyAbsorbingInverseIterate`
itself is not machine-checked and remains an open `Prop` (`LEAN-F0-8`, still
`READY`, owns formalizing it) — this is consistent with, not a reversal of,
the "open" verdict recorded below in the original entry. Full record:
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

**Revisit trigger.** Historical audit trail, preserved for record and
resolved within this same entry — not a live future trigger. **Audit
returned 2026-08-04: `NOT LOCATABLE`.** No such theorem was found under that attribution — every Solan quitting-game paper and
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

### `LEAN-P0-8` — joint complementarity, and absorption derived rather than assumed

- **Status:** DONE (`M+L`), 2026-08-05
- **Lane:** P0
- **Depends:** the fixed-opponents stage primitives; the cyclic-block predicate.
- **Record:** this file

**Objective.** Give the repository a predicate for "an arbitrary infinite row
sequence is complementary in every coordinate", and decide whether absorption
follows from optimality.

**State.** Both landed in `QuittingJointComplementarity.lean`, `sorry`-free.

The predicate closes a **structural absence**: the tree had only a
single-coordinate live-value notion and a periodic-only cyclic-block notion, so
claims quantified over "every complementary sequence" — which several recent
results are — **could not be stated at all**. They now can. The tail value
converges from boundedness alone, with no assumption of eventual absorption, and
the compatibility bridge is proved: a periodic sequence satisfying the cyclic
block predicate satisfies this one. That bridge needed a
uniqueness-of-bounded-solutions lemma and a proof that the periodic extension's
joint survival vanishes from *every* start, not just from zero.

**The new mathematics is the second result: a positive solo reward forces
absorption.** If a sequence is jointly complementary and some coordinate has
strictly positive solo reward, play absorbs almost surely from every time. Every
prior result in this tree takes absorption as a **hypothesis**; none derived it.
Consequently a non-absorbing complementary sequence requires every solo reward
non-positive — close to the zero-solo branch, which suggests why that branch has
the shape it does rather than being a case that happens to be listed first.

The flagged risk — that the tail value's vanishing depends on what the other
coordinates do — resolved without an extra hypothesis, via a sharper tail bound
against a known survival limit rather than against the reward bound alone.

**Acceptance.** Met. Consumers: this discharges the tail-product step of the
isolated-negative floor argument, and makes the universal claims of the carrier
and certification results formalizable for the first time.

### `MATH-P0-5` — is the exact-cycle disjunct complete, or do ε-cycles diverge?

- **Status:** READY — highest-priority item from the Simon 2007 farm
- **Lane:** P0
- **Depends:** `QuittingThreeBranchDisjunction`; Simon 2007 Theorem 3 and its
  post-theorem remark; Solan, *Int. Game Theory Rev.* **3** (2001) 291–299.
- **Record:** [`ephemeral/Simon2007/program-bearings.md`](../../ephemeral/Simon2007/program-bearings.md) §1

**Objective.** Decide whether a weight can exist for which approximate
equilibria exist, ε-cycles exist for **every** ε with minimal length → ∞ as
ε → 0, and **no exact finite cycle exists**.

**State.** This threatens the completeness of the repository's own
machine-checked disjunct, not the conjecture. Simon's Theorem 3 equates
existence with ε-**relaxed** cycles for every ε; the repository's admissible
absorbing cycles are **exact** — terminal `0`-Nash at every phase. Theorem 3
never produces an exact cycle, and its splice direction inherently costs
accuracy. Simon's remark after Theorem 3, citing Solan, states that **the
minimal cycle length may depend on the size of ε**. If length diverges, the
program's "either zero-solo or an admissible absorbing cycle of some finite
length" would be **false** while quitting existence still holds — the reduction
incomplete rather than the conjecture refuted.

**Note the cited source is already on disk**: it is the same Solan paper whose
Theorem 2.1 this program proved false as printed. It may contain the growth
mechanism, and nobody has read it for that.

**Acceptance.** Either a weight exhibiting divergent minimal ε-cycle length
with no exact cycle, or a proof that exactness is recoverable — with the
disjunct's status corrected either way.

### `NEG-P0-2` — the orbit-side counterexample criterion

- **Status:** READY
- **Lane:** P0 (negative lane, complements `NEG-P0-1`)
- **Depends:** Simon 2007 Theorem 3 `(i)⇒(iii)` — whose one uncertified step
  (farm defect register №13, the survival-window landing) **is now repaired**
  (`M [reported]`, Q158) by *continuation lifting*: replace the next-stage
  continuation coordinatewise by `max{r_{i+1,j}, χ_j}`, rational by
  construction, against which the row is still `ε/S_i`-Nash — the deviation
  conditions on reaching stage `i`, not `i+1`, so the circularity that blocked
  the naive repair never arises. General form: `S_i ≥ ε/ρ ⟹ c(p_i) ≥ ρ`, and
  the landing holds for any window `[ρT, T]` under `ρT ≤ 1`, `ε ≤ ρT`,
  `S_∞ < ρT`; the paper's own accuracy carries 4× slack. The inheritance is
  discharged pending formalization; see
  [`SurvivalWindowLandingByContinuationLifting`](../../ideas/UniformEquilibriumLiterature/SurvivalWindowLandingByContinuationLifting.md).
  Defect №12 (`(iii)⇒(ii)`, the asserted constant `1/2`) remains open and
  still touches the equivalence.
- **Record:** [`program-bearings.md`](../../ephemeral/Simon2007/program-bearings.md) §2

**Objective.** Adopt the equivalent orbit-side certificate for refutation:
given no stationary and no instant approximate equilibria, exhibit `ε₀ > 0` and
`B` such that **every** orbit of `F_{ε₀}` through feasible `ε₀`-rational vectors
has total variation `< B`.

**State.** This is a statement about a semi-algebraic correspondence on `ℝ^N`,
plausibly closer to decidable — and to formalizable — than quantifying over all
behavioural profiles, which is what `NEG-P0-1` currently does. It is the
concrete content of the paper's "must involve the topological structure" claim,
and that direction is **argued for quitting games**, not merely asserted.
Conversely any positive proof must construct unbounded-variation orbits, so a
proof strategy that cannot in principle produce them is dead on arrival.

**Acceptance.** The criterion stated in repository vocabulary, and a decision on
whether the search lane should run on it instead of, or alongside, the
behavioural-gap criterion.

### `MATH-P1-5` — audit the decomposition for instant approximate equilibria

- **Status:** READY
- **Lane:** P1
- **Depends:** the stationary repair ladder; the absorbing-cycle carrier; the
  positive-plateau split.
- **Record:** [`program-bearings.md`](../../ephemeral/Simon2007/program-bearings.md) §3

**Objective.** Decide where Simon's third equilibrium family lands in this
program's splits, or record that it does not.

**State.** Simon's trichotomy is stationary / **instant** / orbit. An *instant*
approximate equilibrium is a first-stage profile with some coordinate quitting
with certainty, followed by punishing that coordinate down to its min-max value
plus ε if it failed to quit — a `2ε`-equilibrium. It is neither stationary nor
periodic-cycling here: a period-one cycle does not capture the off-path
punishment clause, and the frontier's falsifier list does not name the family.
It arises exactly when one-stage ε-equilibria have quitting mass tending to one
— the `q → 1` boundary where compactness arguments degenerate.

**Acceptance.** Either a demonstration that an existing branch absorbs it, or
its addition as a named case.

### `LEAN-P0-7` — two-clock punishment for the deviation-cap constructor

- **Status:** READY
- **Lane:** P0
- **Depends:** `Uniform.lean`'s deviation-cap constructor (the program's
  standing intentional placeholder).
- **Record:** [`program-bearings.md`](../../ephemeral/Simon2007/program-bearings.md) §8

**Objective.** Evaluate Simon's Proposition 3 punishment design against the
constructor's intended interface before attempting the placeholder.

**State.** Proposition 3 runs punishment off **two stopping times per player**:
one when the deviation ledger crosses ε — too much extracted by continuing —
and one when *planned* survival drops below `ε/M`, so the plan says the player
should already be gone and mere presence is proof of deviation, **requiring no
statistical test at all**. Punishment fires at the minimum across players with
slack `ε/10`. The second clock covers exactly the tail where absorption is
nearly exhausted, which is the regime this program's exceptional-deviation cap
already addresses.

**Acceptance.** A verdict on whether the two-clock design fits the constructor's
interface, and if so a proof plan for the placeholder that uses it.

### `ENG-P1-3` — dependency drift, and an over-specific upstream lemma

- **Status:** READY
- **Lane:** engineering
- **Depends:** the `InformationTheory` dependency.
- **Record:** this file

**Objective.** Two items on the same dependency.

**(a) Manifest sync.** The `InformationTheory` dependency was added
deliberately, for two entropy experiments. The build's "manifest out of date"
warning is therefore expected, not drift; the residual action is only to sync
the manifest so the warning stops masking a real one later. That is a
dependency-level command and belongs to whoever runs the full build.

**(b) An upstream lemma is stated too narrowly to be reused.** The Gibbs
log-ratio nonnegativity result there assumes **normalized** measures. A second
consumer needed it for an *unnormalized* double sum over edges, could not use
it, and reproved the termwise bound independently — so the tree now carries two
proofs of the same inequality for want of one hypothesis.

The general form reportedly needs only that the two masses agree
(`∑p = ∑q`), with no normalization, and would cover both consumers. That is
strictly more general at no evident cost.

**Acceptance.** The pin resolved, and either the upstream statement generalized
or a local unnormalized variant landed with both consumers pointed at it.

**Why this is tracked rather than dispatched:** the lemma is not in this
repository, so changing it is a dependency edit, and the same dependency is
currently in flux. Sequencing matters.

### `ENG-P2-1` — break the sure-exit cross-check cycle to deduplicate the six pureSetRoot lemmas

- **Status:** DONE 2026-08-05 (production `258d8b5`) — the cross-check
  theorem moved next to its table, the cycle broken, all six lemmas
  deleted with their 18 uses rewired or inlined, no statement changed;
  root build and both gates green.
- **Lane:** engineering
- **Depends:** nothing
- **Record:** this file

**Objective.** `QuittingSureSetRepairFullIntervalCounterexample.lean` carries six
file-local `pureSetRoot` lemmas (definitions around lines 370–452) that are
subsumed by the general versions in `QuittingSureExitSet.lean`. They cannot be
rewired today: `QuittingSureExitSet.lean` imports the counterexample file for
its own cross-check section, so the reverse import is a direct two-module cycle
(verified by attempting it — `lake` reports the cycle). All 18 references to
the six names are internal to the counterexample file, so once the cycle is
broken the deletion is mechanical.

**Plan.** Move the cross-check section of `QuittingSureExitSet.lean` (the part
consuming `not_isεAsymptoticNash_directPureSet`) into the counterexample file
or a third module that imports both; drop the import at
`QuittingSureExitSet.lean:10`; then delete the six lemmas and rewire their
in-file uses to the general versions.

**Acceptance.** The six lemmas gone, no duplicate statements across the two
modules, both modules and the root build green, axiom audit unchanged.

- **Status:** ACTIVE (first entity in flight)
- **Lane:** F0
- **Depends:** `Math/CyclicMaxAffineBound`; the isolated-coordinate anchor
  iterate; `QuittingRelaxedCycleGainIsolatedCoordinate`.
- **Record:** this file

**Objective.** Distil recurring mechanisms into named mathematical objects with
their regime dichotomies and fences, rather than rediscovering them per site.

**The test for when a mechanism earns a name: repetition *with error*.** A
mechanism appearing many times is a pattern; one that appears many times and
produces *mistakes* is an object with no name, and the mistakes are the shape of
the missing definition. Each entity below is nominated on that basis, with the
incident count.

**Entity 1 — the anchored max-affine value. `IN FLIGHT`, four incidents.**
The operator `Φ(w) = max{A, T + P·w}` with a boundary payoff `b`, and its value
defined as the least fixed point dominating `b` — equivalently the limit of
`Φ`-iterates from `b`, which is what a supremum over strategies computes,
including the never-act option. Regime dichotomy: at `P < 1` a contraction with
a unique fixed point and a correct `1/(1-P)` closed form; at `P = 1` a **ray**
of fixed points where the recursion determines nothing and any
division-by-`1-P` formula is meaningless — silently returning a wrong member
under `x/0 = 0`.

Its four incidents: a published theorem false as printed, because its proof
consumes a homogeneous boundary term that does not vanish when survival fails to
decay; a repository closed form proved to give the wrong value in exactly this
regime; a self-consistent terminal value left undetermined on non-absorbing
arrays; and a weight whose repair works by *escaping* the regime rather than
solving inside it. The correct mechanism already exists but is game-local and
unnamed (the solo-quit anchor iterate). The deliverable includes a **fence
theorem** making the closed-form disagreement a corollary rather than a bug.

**Entity 2 — a device with a designed quotient. `IDEA` (seal `I`), three
instances.** A correlation, randomization, or padding device carries a
guarantee relative to a quotient of its realizations, and the guarantee survives
strategic embedding only under quotient measurability on *both* sides. Recorded
as prose at
[`DeviceGuaranteesNeedQuotientMeasurabilityOnBothSides.md`](../../ideas/StrategicCorrelationCommunication/DeviceGuaranteesNeedQuotientMeasurabilityOnBothSides.md).
The entity would be a device-with-quotient structure plus a transport theorem.
**Possibly premature** — the three instances live at different levels of the
tree, and forcing one type over them may cost more than the prose. Nominate
properly only if a fourth instance appears or one of the three needs the
statement formally.

**Entity 4 — rank of the punished coordinate's decision process. `IDEA`
(seal `I`), one incident, externally corroborated.** Simon 2007 isolates why
stagewise-to-global upgrades fail in general and why quitting games are exempt:
the punished player's decision process has **rank 1**. His Example 1 is the
canonical stress shape — a δ-balanced, stagewise-ε-optimal process on an
interval with absorbing ends whose cumulative deviation ledger reaches a
macroscopic gain with probability one half. Any lemma here capping global
deviation gain from stagewise caps must carry a rank or finite-partition
hypothesis or fail on that shape. Nominated because the concept is currently
unnamed on both sides.

**Entity 3 — boundary-generated debt. `IDEA` (seal `I`), may be absorbed.**
That *all* positive debt in the exact-`D` grammar originates at the terminal
mismatch and is transported back. Half-named already by the landed transport
law. **Check whether entity 1 subsumes it before building anything**: "what the
deviator obtains after the array ends" is exactly an anchor, so this may be the
anchored value under another description rather than a second object.

**Acceptance.** Each entity is either landed with its dichotomy and fence, or
recorded as declined with the reason. An entity that nothing consumes is a
regression — the tree already carries one misnamed predicate with zero importers
outside its own file, and a second is not wanted.

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

- **Status:** PARTIAL (2026-08-05) — clause map produced, three of four live
  cells left `open`; see the fence below
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

**Fence — both sources now read; the map is partial, with real gaps, not a
forced alignment.** Both sources are recorded in
`references/20-nonzero-sum-equilibrium.md`. Solan–Vieille 2001 Prop. 2.13 is
`[primary]` — full text of both the working paper and the published version
read; it turned out to be a terminal-payoff/uniform-equilibrium **bridge
lemma**, not a structural characterization, and its numbering does not exist
in the 1998 working paper at all (added at publication). Simon 2007's
Theorem 3 is now `[primary]` too — full text obtained and read (pp. 1, 5,
13–20, 24; the PDF's symbol fonts carry no ToUnicode map, so quotes are
transcribed from rendered page images, not the `pdftotext` layer). Theorem 3
is confirmed **general** (arbitrary quitting games, not escape-game-scoped),
proved from §4.1–4.3 before §5's topology is introduced — the earlier
"plausibly the general principle" inference is now settled, in AGKRS's favor.

The clause map is done and recorded in the same file, in a dedicated
"clause map" section following the Theorem 3 content: S.1 (stationary
`ε`-equilibrium) and S.3 (absorbing profile, all players sequentially
`ε`-perfect) each have a **one-directional, proved** correspondent in the
repository (zero-solo ⟹ S.1; admissible cycle ⟹ S.3, via a definitional match
between Simon's `E_ε` and AGKRS's Definition 3.1), but neither is an *iff*,
S.2 (instant equilibria, keyed to the full stochastic game's min-max value)
has **no** counterpart anywhere in the repository's current vocabulary, and
the repository's own third branch (isolated-negative) has no counterpart in
AGKRS's trichotomy — it is a per-block failure diagnostic internal to the
repository's cyclic construction, not a residual case Simon's or AGKRS's
proofs leave open. **The "internal completeness ⟺ quitting conjecture"
consequence this item flagged does not follow from the map as found, and is
not claimed.**

**Acceptance.** A clause-by-clause map with each correspondence either proved,
refuted, or explicitly open, plus wing records for whichever source the
argument leans on. **Met**, with three of four live cells left `open` (S.1
and S.3 one-directional only; S.2 and isolated-negative uncorrelated) — see
the wing record for the reasoning behind each verdict.

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
- **Depends:** Q148's normal form of the isolated cycle; `K1`–`K2` (Q148's
  own numbering — distinct from Q159's `K1`/`K4` below and from
  `InvertedCounterexampleSearch`'s `K1`/`K4`).
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

**Both objects now exist (`L`), and the projection repair is refuted.**
`ActionLegalityBehaviorTransfer.lean` assembles the padded game as an actual
`StochasticGame`, lifts agreement from a single stage to whole trajectories --
equal history distributions and payoffs at every horizon for any profile that
plays only legal actions -- and closes the legality-restricted transfer in both
directions as genuine `iff`s.

What that leaves is exactly the unrestricted direction, and one candidate repair
is now closed rather than merely doubted. Projecting an unrestricted witness by
mapping each behavioural mixture through the normalization **provably fails**:
the induction needs the projected profile evaluated at an already-normalized
history, which requires the original profile's value at the corresponding *raw*
history, and `normalizeAct` is non-injective -- every illegal action at a state
goes to the same legal one -- so the raw history is unrecoverable. The
obstruction is therefore not the signalling intuition alone but a definite
failure of information recovery, and it lands precisely where the row already
said it would: normalized-action histories.

**Normalized histories are built, additively (`L`), and the obstruction is now
localized.** `ActionLegalityNormalizedHistory.lean` gets them as a *subtype*
rather than a quotient — stagewise normalization is idempotent, so each class
already has a canonical representative inside `Hist`, and everything stays
within the existing `histDist`/`totalPayoff` machinery. No core type changed.

Three things are proved. Two raw histories with the same normalization induce
the *literally same* one-stage continuation for a label-blind profile, and the
padded game's `histDist` pushed forward by normalization satisfies the same
one-step recursion as `histDist`. Payoff bookkeeping is normalization-blind for
**any** profile, since the padded stage payoff normalizes idempotently. And
label-blind strategies are characterized exactly — invariance is equivalent to
factoring through the normalization, via a mutually inverse pair with strategies
whose domain is the normalized history type.

The payoff transfer remains open, with a sharper diagnosis: a single raw label
is unconditionally payoff- and transition-free, but this does not extend to a
multi-stage cap even with the prescribed profile strengthened to invariant.
Bounding an arbitrary deviator needs a matching legal one, and the
pointwise-normalized candidate is evaluated along *its own* trajectory at
already-normalized histories — the same non-injective inversion. So **the
obstruction lives entirely inside the deviator's own strategy and does not
depend on opponent behaviour**, which is a strictly stronger localization than
the signalling reading.

**Disintegration works (`L`), and the row now reduces to one question.**
`ActionLegalityDisintegration.lean` conditions an arbitrary deviator's realized
action on the normalized history instead of projecting pointwise, which defeats
the non-injective inversion outright. Against a background profile that is both
label-blind and legal, the disintegrated deviator's raw trajectory equals the
original's pushed forward along normalization — for a **literally unrestricted**
deviator, no strategy-class restriction anywhere. Combined with
normalization-blind payoff bookkeeping this gives **exact payoff equality** at
every horizon and player, not merely domination. The construction is total,
including at normalized histories of probability zero.

**The honest residual is *legality*, not blindness.** The assembled target
theorem binds a label-blindness hypothesis and **never uses it** — the proof
runs on legality alone. So the row reduces to:

> can a padded-game equilibrium be taken **legal** without loss?

**ANSWERED: NO (`M [reported]`, Q157).** Padding with raw-action histories is
**unsound**: a sharp minimal system — two players, two states, one two-element
duplicate fiber per player — has reduced attainable set `{(0,0),(1,1)}` and
enlarged attainable set the whole diagonal segment. The duplicate labels carry
a jointly controlled lottery (`Z = B₁ ⊕ B₂`, unbiasable unilaterally), and
reduced profiles, whose live-path history is forced, are held to independent
products: the always-continue deviation collects `√p` against target `p`. No
cheap hypothesis rescues it — two players, fiber size two, and one non-identity
action already fail. The conditional transfer (label-blind + legal witness)
stands untouched; the unconditional step is dead.

The repair is exact but changes the game: record **normalized** actions in
histories, i.e. the quotient must be baked into the game's own monitoring, not
recovered afterwards — which is what the normalized-history subtype was built
for. Consequently the route from the state-independent conjecture to
state-dependent action sets goes through the normalized-history padded game or
through generalizing the conjecture to dependent action types directly; the
raw-history padding route is closed. See
[`DuplicateActionLabelsCarryAJointlyControlledLottery`](../../ideas/StrategicCorrelationCommunication/DuplicateActionLabelsCarryAJointlyControlledLottery.md).

Blindness is what the *disintegration route* needs, not what the target needs,
and conflating the two overstates what is open. The obstruction to blinding is
nonetheless machine-checked rather than argued: the induction needs the
background profile already invariant to rewrite the one-stage kernel as a
function of the normalized history alone; disintegrating the deviator's
coordinate alone leaves the others free to leak labels; disintegrating all at
once against an already-invariant background is circular.

Two consequences worth acting on. The disintegration module currently feeds one
unconsumed inequality, since the target does not need it. And an "`ε`-Nash
against the legal shadows of all unrestricted deviations" notion is one
quantifier away and undefined — that is plausibly the statement the row actually
wants.

**The chain is more general than its statement.** Legality is never used either,
only componentwise idempotence of the normalization: the whole development is an
idempotent-relabeling theorem that happens to be instantiated at legality.
Finiteness is likewise an artifact of one conditional-distribution lemma; a
countable-support version would remove it.

Note the disintegration identities require finite state and action carriers,
stated explicitly and used nowhere upstream.

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

### `LEAN-P1-1` — retargeted: the n≥3 blocker-designation lemma, after the capstone closed n=2 by a different route

- **Status:** READY
- **Lane:** P1
- **Depends:** `le_of_lt_affine_on_unitInterval` (landed,
  `QuittingTwoPlayerExistence.lean`); the general sure-exit-set theorem.
- **Record:** [Two-player is
  closed](../../ideas/TwoPlayerBaseCaseExhaustion/TwoPlayerQuittingIsClosed.md)

**Objective (retargeted).** The original aim — a source-aligned six-scalar
proof that every two-player quitting game has stationary terminal epsilon
equilibria — is **refuted as a complete route, even at `n = 2`**: the
capstone's docstring exhibits a two-player weight,
`r({owner}) = (1, −2)`, `r({blocker}) = (0, −1)`,
`r({owner,blocker}) = (−1, 0)`, with no exact stationary equilibrium anywhere
on the rate square (hand-checked over all four corners and the interior), so
genuinely non-stationary approximate equilibria are mandatory for some
weights. `n = 2` itself is independently and unconditionally closed by
`quittingGame_exists_uniformEquilibriumPayoff_twoPlayer`
(`QuittingTwoPlayerExistence.lean`), via branch classification (zero-solo,
solo-quitter rate, pair-repair, joint-exit) rather than the six-scalar route,
and needs no further work under this row. What survives here is the forward
direction mined from that proof: generalize blocker designation to `n ≥ 3` —
finitely many opponents plus affine-in-`p` failure of the no-join condition
forces one opponent to block on all of `(0,1]`, and
`le_of_lt_affine_on_unitInterval` nearly suffices as is.

**State.** `READY`. What breaks past `n = 2` is the pair-repair branch:
coalitions of size `≥ 2` open internal-leaver deviations and spectator
preemption that the two-player proof never enters — the precise `n = 3`
frontier the mined map identifies.

**Acceptance.** Blocker designation restated and proved at general `n`; the
general sure-exit-set theorem ("no member leaves, no outsider joins",
arbitrary coalition `S`) stated — one instantiation away from landed
machinery.

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

### `LEAN-P0-9` — machine-check the weight with relaxed cycles at every tolerance and no exact one

- **Status:** IN FLIGHT
- **Lane:** P0
- **Depends:** the complementarity predicate, the transport law.
- **Record:** [exact-vs-relaxed]

**Objective.** Machine-check that an explicit rational three-coordinate cyclic
weight admits no exact cycle of any finite period, while admitting relaxed
cycles of period `3m` for every `m`.

**State.** `IN FLIGHT`. The hand proof is complete and finite: centered values
are nonnegative since every reward to `i` from an outcome containing `i` is at
least `-1/2`; the local gain identity forces at most one positive coordinate per
exact row; singleton rows pin the active coordinate's centered value to zero
while forcing the predecessor's strictly positive; the coordinate sum is `1/2`
at every phase, which the block-endpoint vertices cannot meet. The row
dichotomy alone is purely algebraic and is the first landing target.

**Acceptance.** **PARTIAL, 2026-08-05**, `QuittingCyclicWeightRowDichotomy.lean`.
The row dichotomy is proved: every exactly complementary row of this weight has
at most one positive coordinate. The gain identity was **proved against the
table, not assumed** — an independent hand re-derivation mis-copied an entry and
the proof would not close until it was corrected against the source, which was
right.

The periodic half remains: singleton rows pinning the active coordinate's
centered value to zero while forcing its predecessor's strictly positive, the
phase-invariant coordinate sum, and the block-endpoint vertex contradiction.
That half needs block machinery the row-level file does not have, and it is
blocked on `LEAN-P0-11` if it is to say anything about the Bool-valued
development.

### `LEAN-P0-10` — separate the three contraction deficits and price re-closing

- **Status:** DONE
- **Lane:** P0
- **Depends:** the transport law, the survival-prefix bridge, the anchored
  max-affine object.
- **Record:** [anchored-repair]

**Objective.** Formalize the exact residual formula for closing a modified
block, and machine-check that the same formula **fails** for the optimized
deviation objective.

**State.** `DONE`. Three deficits must not be conflated: the value recursion's,
the deviation recursion's built from deleted products, and a local block's
transported mass. The law is an exact identity for the first, a sharp upper
bound for the second, and false for the third. Prefix survival is a
multiplicative transport factor, never a denominator.

**Seals differ by leg.** The exact identity and the falsity witness are `L`. The
**sharp middle leg is `M [reported]` and has no theorem** — the formalization's
middle deliverable was the transport split, not a bound on rowwise
complementarity loss. Do not cite the three legs under one seal.

**Acceptance.** **DONE, 2026-08-05**, `QuittingSeamPriceResidual.lean`. All four
parts landed. The exact form needed no hypothesis beyond the definitions — the
successor payoff is affine in the tail value with slope the full joint continue
mass, unconditionally. The failure witness is an isolated coordinate at hazard
rates `1/2` and `1/3`, where the mismatch is rate-independent while the full
deficit varies, so no single numerator reproduces it; the deleted deficit there
is exactly `0`. Unit continue mass makes the successor map the identity, so
vanishing absorption gives no pole.

### `LEAN-P0-11` — bridge the two encodings of complementarity

- **Status:** DONE
- **Lane:** P0
- **Depends:** `QuittingCyclicWeightRowDichotomy.lean`, the Bool-valued spine.
- **Record:** this file

**Objective.** Prove that the real-valued hazard encoding of the gain and
complementarity conditions agrees with the Bool-valued mixture encoding the main
development uses.

**State.** `DONE`, and this was a duplication introduced deliberately and
knowingly. The questions corpus states everything over arrays of reals; the Lean
development states everything over `PMF Bool` mixtures. Formalizing a question's
answer therefore produced a **second** encoding of `Σ_i`, `Γ_i`, `g_i` and
exact complementarity, generic over a finite index type. Both are correct and
neither can currently feed the other.

Until the bridge exists, a theorem proved in one encoding says nothing about the
other, and a reader may reasonably assume otherwise. That is exactly the shape
that rots.

**Acceptance.** **DONE, 2026-08-05**, `QuittingHazardRowBridge.lean`. The
encodings are **equivalent**, not merely analogous: quit payoff, continue
payoff, and endpoint difference agree exactly with the real-valued `Σ`, `Γ`, `g`
for every reward and continuation value, with no sign or scope mismatch and no
extra hypotheses. Exact row complementarity corresponds to zero-error root
endpoint Nash in both directions, which the development already identifies with
exact root Nash. The row dichotomy transports as a demonstration.

The proof needed one new combinatorial lemma: the expectation of a family of
independent Bernoulli coordinates expanded as a powerset sum.

One asymmetry, recorded rather than hidden. Mixture to hazards is total; hazards
back to a mixture needs the row in the unit interval, since the polynomials stay
meaningful outside it but no mixture realizes such a row. Harmless where used,
and it means results proved over unrestricted real rows do **not** automatically
transport.

### `LEAN-P1-5` — linear complementarity infrastructure

- **Status:** DONE — `Math/LinearProgramming/SingletonLCP.lean`. Predicate,
  scaling/permutation invariance, the support-pattern reduction, the
  game-facing instantiation, and a closed-form two-coordinate
  characterization with no residual existential. Decidability for rational
  data is **blocked, precisely**: the Fourier–Motzkin/Farkas material is
  Prop-level, not computable; a `Decidable` instance is a separate project.
  The absorption equivalence (`K4`, Q159 §5's numbering — "the relaxed
  compiler", distinct from Q148's `K1`–`K2` above and from
  `InvertedCounterexampleSearch`'s `K1`/`K4`) is now stateable.
- **Lane:** P1
- **Depends:** none.
- **Record:** [exact-vs-relaxed]

**Objective.** Provide the normalized singleton LCP as a Lean object with a
feasibility predicate.

**State.** `DONE`. Several recorded results turn on the feasibility of
`λ ∈ Δ(I)`, `q = Bλ ≥ 0`, `λᵢqᵢ = 0` with `Bᵢⱼ = rᵢ({j}) - rᵢ({i})` — in
particular the equivalence deciding whether absorption can vanish, and with it
whether a diverging period is even possible. **LCP infrastructure now exists**
in `Math/LinearProgramming/SingletonLCP.lean` (`SingletonLCPFeasible`, its
scaling/permutation invariance, the support-pattern reduction via
`singletonLCPFeasible_iff_exists_supportPattern`, and the game-facing
`quittingSingletonLCPFeasible`); the residual-class material stays an ideas
group, not Lean, but formalizing the absorption-vanishing equivalences is no
longer blocked on the predicate itself.

**Acceptance.** The predicate and enough API to state the absorption
equivalence. Decidability for rational data would be a genuine strengthening,
since it turns the criterion into something checkable on a concrete table.

### `MATH-P0-6` — port the all-periods non-existence theorem

- **Status:** DONE
- **Lane:** P0
- **Depends:** `LEAN-P0-9`.
- **Record:** [exact-vs-relaxed]

**Objective.** ~~Machine-check that the `ε`-perturbed cyclic three-player weight
admits no exact cycle at any period.~~ **DONE, end to end, 2026-08-05.**
`PerturbedCyclicWeightNoExactCycle.lean` (the label lock, real encoding, with
the `ε = 0` witness and mechanical verification that positivity is needed)
plus `PerturbedCyclicWeightCycleExistenceHoleOccupied.lean` (the cycle-level
transport and the statement against the trichotomy's own predicate:
`¬∃ terminal, IsQuittingCyclicContinuation (ftvRewardEps ε) terminal`,
`ε ∈ (0,2]`, weight alignment machine-checked entry-for-entry). The leading
hard candidate provably lies outside the trichotomy; the cycle route's
incompleteness is an internal theorem, and the published chain is independent
confirmation only.

**State.** `DONE`, and the motivation was settled rather than speculative
before the last piece landed: that weight already **occupies** the
trichotomy's cycle-existence hole. Its solo
values are all `1 > 0`, so the zero-solo branch fails; period one is excluded by
the affine no-join condition, which at one coordinate pair reads `1 + pε ≤ 0`;
period three is excluded because the unperturbed phase-rotation block acquires a
strictly profitable deviation of exactly `ε/2`. Only the all-periods statement
is missing, and it is the published paper's actual contribution — its own
`ρ`-argument through a chain of six lemmas. Nothing weaker suffices, since the
two computations above cover two periods.

The comparison is sound. The terminal payoff is not a surrogate: finite-average
payoff converges to it unconditionally for every profile including off-path
deviations, so an absorbing cyclic continuation block is the same object as the
literature's completely absorbing admissible sequence.

**Acceptance.** The non-existence theorem for this weight at every period, for
`ε ∈ (0, 2]`, via the floor + row dichotomy + label lock. The formalization
must **fail at `ε = 0`** — a cycle exists there — and the point of failure must
be the predecessor-value strict inequality, which is where `ε` enters. The
published theorem remains as independent confirmation only.

### `MATH-P0-7` — a sufficiency theorem for the isolated-negative branch

- **Status:** READY
- **Lane:** P0
- **Depends:** the trichotomy.
- **Record:** [exact-vs-relaxed]

**Objective.** Show that a weight in the isolated-negative branch has a uniform
equilibrium payoff, or exhibit one that does not.

**State.** `READY`. This is the trichotomy's other hole and the sharper of the
two: the branch is reachable — the refutation witness lies in it — but carries
no sufficiency theorem, so a weight landing there gets nothing. One specific
two-coordinate weight is repaired by a symmetric contracting perturbation that
keeps both opponents' continuation mass strictly below one, avoiding the `ε = 0`
degeneracy of the exact isolated configuration; that construction is explicitly
stated not to generalize.

**Acceptance.** A general theorem, or a counterexample. Since the branch's
mismatch is exactly `-r_i({i})` at the isolated coordinate, the perturbation
must trade that fixed mismatch against the continuation mass it frees, and any
general argument has to control that trade rather than compute it on one table.

### `MATH-P0-8` — the relaxed compiler: formalize Proposition 3

- **Status:** READY
- **Lane:** P0
- **Depends:** phase-switch engine, `quittingPlannedSurvivalStoppingIndex`,
  punishment floor, the ε-bridge, the reached-stage transfer (in flight).
- **Record:** [`SurvivalWindowLandingByContinuationLifting`](../../ideas/UniformEquilibriumLiterature/SurvivalWindowLandingByContinuationLifting.md), Q158

**Objective.** The per-tolerance existence engine: an `ε`-rational chain with
divergent quit mass whose consecutive values are `δ`-linked compiles to a
`3ε`-equilibrium, via punish-at-a-clock.

**State.** `READY`, and this is the decisive chunk. The four no-gos of this
wave jointly force any closing proof into exactly this architecture: per-`ε`
families of unbounded period, an off-path punishment component, deviation
pricing in the deleted deficit, and no compactness/budget/projection shortcut.
Component inventory: phase-switch wrapper landed; stopping index `i♯` landed;
punishment floor landed; ε-bridge landed; reached-stage transfer in flight.
**Missing**: ~~the cumulative-advantage ledger `W` and its index `i*`~~
(**landed**, `QuittingLedgerPunishClock.lean` — summand pinned to the deleted
normalization, clocks and combinator, Abel cash-out, the assembled cap
consuming a ledger condition); the rank-one decision-discrepancy argument and
the "only repetitive continuing matters" deviation reduction — **both now
posed as Question 161** (the DDP maximal inequality, the rank-variation
bound, the rank-one corollary, and the domination consequence with the
unrestricted deviation quantifier made explicit — the step the architecture
guard warns about is Part D, and the question says so); plus the small
residuals: **ceiling-IR punishment attainment and Case-2 wiring landed**
(`QuittingPhaseSwitchResiduals.lean`); the truncated-ledger transfer's
premise is **false** — the seed discrepancy at the truncation back-propagates
geometrically, leaving a survival-weighted correction at every prefix index —
and its honest form is a folding lemma riding the assembly's own
reach-probability bounds (Case 1 via Q161's corollary, Case 2 via the wired
clock), to be landed once Q161 returns.

**Acceptance.** The compiler as a theorem consuming a per-tolerance family and
producing the terminal `ε`-Nash objects the selection theorem eats. Landing it
replaces the exact-cycle branch wholesale.

### `MATH-P0-9` — the lock/unlock dichotomy for orbit variation

- **Status:** ANSWERED IN PART — conditional circulation producer LANDED;
  arbitrary-weight certificate production remains open.
- **Lane:** P0
- **Depends:** the label lock (`L`), transported leverage, the
  survival-window landing.
- **Record:** this file; [circulation payoff interface](CirculationUniformPayoff.md);
  Q159; the two seals
  [`WeightedOneStageNashCannotPriceMotion`](../../ideas/UniformEquilibriumLiterature/WeightedOneStageNashCannotPriceMotion.md)
  and
  [`SingletonFaceCirculationsSteerOrbits`](../../ideas/QuittingGameConjecture/SingletonFaceCirculationsSteerOrbits.md).

**Production update (2026-08-07).** The multi-owner circulation case is now
landed: a supplied bounded `FaceCirculationCertificate` with ratio ceiling
below one and punishment-valid floor is a genuine producer through compact
chronological path selection and the support-witness compiler. It remains
conditional and does not manufacture certificates for arbitrary weights.
The §2.1 absence proofs, pinned-pure decoupling lemma, and certificate search
remain research work. Questions filed:
**Q162** — the true min-max of a quitting weight (stationarity of the worst
plan, the finite reduction, the three named tables including `F′`'s
diagonal-tightness suspicion, and the three consumer shapes) — and **Q163** —
support purification or the weighted lemma (the one unsound joint left in
the equivalence's hard direction, with the published-lemma verdict as its
Part D). Deferred deliberately: the branch-three sufficiency question, which
should be posed *after* Q162 returns, since its mismatch is ceiling-minus-
honest-value and the true `χ` reshapes it.

**Q159's verdict reshapes this row.** The dichotomy as posed was the wrong
axis: the granted motion constant is **false on the weighted one-stage
correspondence** (tremble counterexample at the scaled cyclic weight), so
quit mass and variation decouple there, and every future motion argument
must declare its correspondence — support-perfect (constant plausible,
membership transfer from global equilibria unproven) or weighted (no motion
floor). Locks split into motion locks (control only overlap mass) and sealed
locks (imply an instant branch). The **constructive replacement** is now the
multi-owner face-circulation theorem: a supplied finite certificate yields
balanced rational orbit data, compact chronological support paths, and a **new
conditional existence class**. The machine-checked theorem requires a bounded
certificate, phase-ratio ceiling strictly below one, and a floor above formal
punishment values; it does not solve arbitrary weights. Certificate search over
the remaining families, the missing branch (strict local continuation rests
with diffuse trembles), and support-purification transfer remain open steps
toward all weights.

**Objective.** Decide the conjecture: on a weight with no stationary and no
instant approximate equilibria, either some coordinate's value can lock (and a
lock-adjacent branch applies), or every exact-complementarity attempt forces
value handoffs, and each forced handoff contributes a quantified variation
increment — so relaxed-cycle families of unbounded variation exist.

**State.** `READY` as a conjecture; this is the program's attack on the open
residue — producing the unbounded-variation orbits that the repaired published
equivalence converts into equilibria. The label lock is the first
machine-checked instance of the locked side; the postulation is that its
negation is generative. The leverage and landing lemmas are the calculus for
"forced handoff implies a variation quantum."

**Acceptance.** Either direction advanced honestly: a lock classification, or
a handoff-to-variation lower bound on an explicit class. This row is a
research direction, not a port; scope accordingly.

**Quantitative companion (backward-error lens, `ephemeral/NumericalAnalysis.md`
§1).** The conjecture that `d(ε,δ)` — minimal relaxed period at tolerance —
is governed by the conditioning of the exact-cycle strata: the least `L`
whose stratum passes within backward-distance `δ` of the weight. Three
independently-derived quantities appear to be one: the backward condition
number `1/min(yᵢ, 1−yᵢ)`, the lock margin, and the `ε`-bridge's weighted-gain
weakness at extreme hazards. If that identity holds, the lock/unlock
dichotomy and the `d(ε,δ)` law are two faces of stratum geometry, and a Q159
trap is a weight at uniformly positive backward distance from every
low-period stratum. The numerical signature test on the period-`3m` family is
in flight from the intake note; its output should be read against this row.

**First signature results (`Γ_η`, `η = 1/8`, `m = 1..8`, discovery-grade,
frozen values).** The defect tracks the documented `η·log2/(3m)` asymptotic
(ratio `0.72 → 0.96`); the best single own-set shift leaves a residual of
**exactly half** the defect at every `m` (ten digits) — a hard floor, read as
Chebyshev centering of sign-alternating phase defects; and the four-parameter
refinement is brittle, feasibility flipping with arithmetic accidents of `m` —
the overdetermination signature. Within this construction family the backward
distance to `Σ_{3m}` is therefore of order `1/m`, which under the
stratum-conditioning conjecture predicts the **linear** `d(ε,δ) ~ 1/δ` law
for `Γ_η` — upper-bound-family evidence only; a faster-approaching family
would restore the `log` option. The exact `½` wants a proof: the predicted
mechanism is **seam localization** — per-player defect concentrated at the
handoff phases and near-zero mid-block, so a uniform own-set shift can only
center the seam against the block, optimum at half. Checkable immediately by
printing per-phase defect vectors, and provable-looking from the family's
closed form. Frozen values remain the standing caveat: the honest
linearization couples the perturbation through the value recursion, and the
fixed-tail vs cycle-feedback gap is the same three-legged split the seam-price
law had.

### `GEN-P1-1` — the positive-recursive program (V5), scoped

- **Status:** PLANNED — general lane, behind the quitting core.
- **Lane:** P1 (general conjecture); calibration probe complete.
- **Record:** the scoping report, distilled here; the [pr] claim file's
  acceptance line corrected (vacuity).

**Scoping verdict (2026-08-05).** The framing inverts: **Theorem 2.8 is
vacuous on quitting games** — a quitting game's `B` is the all-continue
singleton with rectangular component, and the rectangular case is exactly
what the source cannot do. So the class is *disjoint from* the quitting wing:
reuse is broader than expected on general engines (`PunishmentLevel`,
`Feasible`, `Fink`, the germ/curve-selection wing, the terminal-to-uniform
waist) and narrower on constructions (≈250 `Quitting*` files are templates,
not libraries — tied to `Act = Bool` and singleton `B`). The repo has **no
recursive-game class**, a "rectangular" name collision, Kakutani proved but
imported nowhere in `GameTheory/`, and no Everett value theory — and for this
class the min-max needs **Everett, not Mertens–Neyman**: `χᵢ = 0` exactly at
coordinatewise rectangularity, so **non-rectangularity is what breaks the
zero-punishment witness and threats are the substance of the theorem**.

**Plan:** 8 waves to a *conditional* Theorem 2.8 (statement modulo one named
correspondence-selection hypothesis, the repository's established terminal
form) — waves 1–4 low-risk reuse, 5–6 medium (germ transport, the bridge
discharge), 7 high (phase-switch over live *words*, an engine rewrite, since
unique-live-history is false beyond quitting). **Wave 8 — the fixed-point
core — goes to the questions corpus, not to a Lean agent**: over rows with
support constrained by a non-rectangular `B`, does the one-stage
`ε`-perfectness correspondence admit a convex-valued selection? The repo has
already machine-refuted the natural candidate
(`successorImage_not_convex`), so a new device is genuinely required.
Estimated 8–11 waves to the conditional form; the unconditional sits behind
the question.

### `MATH-P0-11` — the minimal open family: the four-player cyclic phase diagram

- **Status:** **SOLVED (followup answer); stress-point cashout LANDED.** The
  scaled-cyclic calibration and repaired four-player stress weight
  `(x, λ) = (2, 1)` now have concrete production uniform-payoff corollaries
  through supplied circulation certificates. The broader followup family
  analysis remains audited mathematics, not a blanket production theorem.
  Its reported claim was that every `F′(x, λ)`
  with `x > 0` admits a **rational singleton-face circulation** with explicit payoff
  `v(x) = (1, 3−2a, 1/a, 1)`, `a` the root of `2a² + (x−1)a − 1 = 0` —
  `λ`-independent payoff, period `O(1/δ)`; `x ≤ 0` has the exact
  opposite-pair equilibrium. Extracted en route, each valuable beyond the
  family: the **exact true min-max** with explicit boundaries (`x = 1/2`,
  `x₊(λ) = 1 − 1/((1+λ)²(2+λ))`) — answering Q162's Part C for this family
  in advance; **no instant equilibrium even with true-min-max punishment**;
  the complete **singleton-carrier lock classification at four coordinates**;
  a hand-assembled local-defects-to-arbitrary-deviations chain (§5, the
  compiler's shape done directly for this family); and the hardest remaining
  stress point for *exact-cycle classification* (not existence):
  `(x, λ) = (2, 1)`, reported circulation payoff `(1, 2, 2, 1)`. At that
  stress point the certificate, formal punishment-floor inequality, and
  uniform-payoff existence are now machine-checked. The compact selector does
  not identify its existential payoff with `(1, 2, 2, 1)`. **Reported
  strategic consequence**: the circulation class swallowed the minimal
  candidate family, including the diagonal-tight-floor case; production Lean
  currently certifies the stress point, not the whole parameter family. The
  counterexample hunt should target weights outside the circulation class,
  whose true boundary remains the sharpest open question.

  Previous state, kept for the record: Q160's family **collapsed by an authoring flaw**
  (all triples zeroed made all-quit a period-one exact subgame-perfect
  equilibrium at the true min-max, everywhere; a lone continuer must face a
  nondegenerate `(n−1)`-coalition payoff, and the sparsity shrink went one
  size too far — the vacuity rule now covers game families). **The repaired
  family is filed as a followup in the Q160 thread** (no separate question
  file) — every coalition pays its outsiders `1` — with
  the trivial witnesses probed in authoring and recorded as supplied facts;
  the open region is `x > 0`. Salvaged from Q160's answer, methods not
  values: the true-min-max computation, the symmetric-stationary
  classification with its tangential bifurcation, the pure-First-set
  classification. New load-bearing subquestion: `F′`'s min-max plausibly sits
  *tight against the diagonal* (best responses to both extreme opponent
  profiles earn exactly the solo value), a structure no solved example has —
  and the circulation-certificate check against `F′` is Part B, either
  solving `x > 0` outright or exhibiting the first natural habitat outside
  the circulation class.
- **Lane:** P0.
- **Depends:** affine invariance (the `d ≡ 1` normalization it legitimizes),
  the lock, the landing, the LCP and solo-quitter criteria, the phase-switch
  engine; the certsearch toolchain sweeps its parameter square.
- **Record:** this file; Q160.

**Objective.** The open problem restricted to its plausibly minimal natural
habitat: the two-parameter family `F(x, ε)` — four coordinates, cyclic,
diagonal `1`, `G_ε`-sparse, with `x` the payoff to the opposite player, the
first genuinely four-coordinate degree of freedom. Solve its `(x, ε)` phase
diagram: solved zones by explicit criteria, the lock's fate at four
coordinates, existence by rotating relaxed cycles under phase-switch
punishment, or the first certified counterexample candidate.

**State.** Every known theorem misses the family for a stated reason
(joining is profitable, four players, not zero-solo; escape-class coverage to
be verified). The class lattice above it: `n = 4` (minimal open count) →
diagonal-normalized (legitimate only by our affine invariance — the
literature could not state this class) → cyclic-invariant (the home of every
known hard phenomenon) → sparse. The anonymous/fully-symmetric class one
level up is a cheap dissolves-or-sharpens test (one-dimensional symmetric
complementarity) worth one probe, no more. **Attribution caveat**: the
family's open status is internal-knowledge, medium-high confidence; a
literature verification is owed before any public claim.

### `MATH-P0-10` — the drift device: uniform threats against moving states

- **Status:** READY
- **Lane:** P0 of the **general** conjecture; explicitly **not** on the
  quitting critical path — a quitting game has one live state and nowhere to
  drift, which is why the entire quitting program runs without this.
- **Depends:** the Puiseux/curve-selection wing (shared with the germ-route
  shortcut), `Kernel.trajMeasure`, the phase-switch engine as the static
  special case.
- **Record:** this file; necessity is witnessed in-tree by the Big Match
  fence — stationary punishment is provably insufficient against drift, so no
  routing around the device exists for threat-based constructions.

**Objective.** The punisher's uniform guarantee for general finite stochastic
games: one history-dependent strategy holding the deviator's average at or
below the min-max plus `ε`, simultaneously at every large horizon, against
state drift.

**State.** Two layers. **BK regularity** — bounded variation of the
discounted value curve as the discount vanishes — is semialgebraic geometry,
the general-state target of the existing Puiseux wing. **The adaptive-clock
potential** — the discount updated by realized payoffs so that patience
absorbs drift — is the genuinely new device: an *adaptive* version of the
phase-switch clock, where ours is static. The honest target is one-sided
(the punisher's guarantee), though the one-sided form is not obviously
easier. The modern textbook proof is the natural farming target before any
Lean is written; the novel-device question — whether the landing lemma and
an adaptive switch clock can produce a potential argument native to this
program's machinery — goes to the questions corpus after the farm.

**Acceptance.** The one-sided uniform guarantee as a theorem, or an honest
partial: the potential lemma over a granted BK-regular value curve, with the
regularity layer tracked separately. Nothing here gates the quitting lane.

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

**The parallel route: the quitting three-branch disjunction (the
trichotomy).** A second, independent path to terminal existence for finite
quitting games, not shown in the diagram above because it does not run
through the compactification bridge.

```text
finite quitting weight
        |
QuittingThreeBranchDisjunction (the trichotomy), machine-checked -------- [L]
   zero-solo  |  admissible cycle  |  isolated-negative
        |             |                    |
   exists_..._of_  exists_..._of_admissible_   MATH-P0-9: the open core
   zeroSolo  [L]   quittingCyclicContinuation   (lock/unlock dichotomy)
                   Block            [L]          -- ANSWERED IN PART (Q159)
        |             |                    |
        +-------------+--------------------+
                       |
        MATH-P0-8: the relaxed compiler (formalize Proposition 3) --
                     converts the open core's unbounded-variation orbit
                     families into terminal ε-Nash objects -------------- READY
                       |
        n = 2 capstone: quittingGame_exists_uniformEquilibriumPayoff_twoPlayer
                     (QuittingTwoPlayerExistence.lean) -- branch
                     classification directly, not via the compiler -------- [L]
                       |
        n >= 3: LEAN-P1-1, retargeted -- blocker designation generalizes;
                     pair-repair (coalitions >= 2) is the open frontier --- READY
```

The capstone answers `n = 2` unconditionally by branch classification, so it
does not itself depend on `MATH-P0-8`; the compiler is the route by which the
trichotomy's open core (`MATH-P0-9`) is meant to close the general case.

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
- The published cycle-existence hole is occupied: a weight from the
  literature (Solan 2001, via AGKRS's reference chain) provably lies outside
  the trichotomy's cycle branch at every period, `MATH-P0-6` landed end to
  end, and the case-2 refutation is restored on an attested basis
  (`PC-010`).
- The two-player capstone landed: `n = 2` finite quitting is closed
  unconditionally by branch classification, independent of the six-scalar
  stationary route that `LEAN-P1-1` originally targeted (refuted as a
  complete route, even at `n = 2`); the mined `n = 3` map retargets that row
  to blocker designation.
- `MATH-P0-9`'s open core was answered in part (Q159): the weighted
  one-stage correspondence's motion floor is false by a tremble
  counterexample. Production `5e7d0e7a` turns any supplied bounded
  multi-owner face-circulation certificate with a punishment-valid floor into
  a uniform-payoff existence result through compact chronological selection
  and the support-witness compiler. Arbitrary-weight certificate production
  and the distinct relaxed compiler (`MATH-P0-8`) remain open.

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
[exact-vs-relaxed]: ../../ideas/AbsorbingCycleCarrier/ExactCyclesAreNotLimitsOfRelaxedOnes.md
[ep]: ../../ideas/PositivePlateauBoundaryClosure/EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md
[gbp]: ../../ideas/VanishingDiscountResponseSynthesis/DiscountedCertificatesConvergeToGainBiasPackets.md
[welf]: ../../ideas/PositiveWelfareSeparator/FailedRepairMayYieldPositiveGlobalWelfareSeparator.md
[cex]: ../../ideas/QuittingGameConjecture/CounterexampleNeedsPositiveBehavioralExploitabilityGap.md
[naf]: ../../ideas/StationaryRepairExhaustion/NaiveStationaryCompactificationNeedNotAttainEquilibrium.md
[ft]: ../../ideas/UniformEquilibriumLiterature/FTVCyclicGameHasNoStationaryApproximateEquilibria.md
[nq]: ../../ideas/UniformEquilibriumLiterature/NonQQuittingGamesHaveUniformApproximateEquilibria.md
[pr]: ../../ideas/UniformEquilibriumLiterature/PositiveRecursiveNonrectangularGamesHaveUniformPayoffs.md
