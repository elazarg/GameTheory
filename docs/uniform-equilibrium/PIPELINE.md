# Uniform-equilibrium project pipeline

**Production-Lean checkpoint:** `14d75ff`; **research-control checkpoint:**
`cd1db11`, both audited on 2026-08-03. **This file revised 2026-08-04.**
Lean work landing after the last audited commit is uncommitted-or-newer and
not yet reflected in these checkpoints.

This is project-control truth: decisions, dependency priorities, gates, and
acceptance conditions. It is not a mathematical exposition. The fixed-cutoff
holonomy compactness work is committed and counted; the marked absorption-path
route is a selected open design, not production mathematics. New Lean files
are never counted as landed until committed, built, and reflected in the
owning claim and [`FRONTIER.md`](FRONTIER.md).

**Handoff validation.** `lake build` succeeds. Local Markdown links under
`docs/`, `ideas/`, and `REORG.md` resolve. The stricter repository audit is
known red, not silently green: it reports four `opaque` declarations, ten
`native_decide` proofs, and 25 tracked Lean modules outside the default import
targets; the two intentional `sorry` declarations are `exists_uniformDeviationCapConstructor` in `UniformExistenceConjecture.lean` and `quitting_zeroSolo_or_admissibleCycle` in `QuittingConjecture.lean`. These are owned by
the engineering queue below and the
[proof-engineering audit](../../ephemeral/ProofEngineeringAudit.md), rather
than blockers hidden in the P0 mathematical status.

## Project-control decisions

| ID | Decision | Rationale | Rejected alternative | Consequence | Revisit trigger |
| --- | --- | --- | --- | --- | --- |
| `PC-001` | Make finite quitting games the primary direct mathematical front. | They are a strict subclass, but a counterexample refutes the universal conjecture and the positive problem now has an exhaustive optimized-debt split. | Treat every stochastic-game architecture as equal priority. | General routes continue in parallel, but cannot displace the quitting P0 hinge by recency. | A quitting solution that fails to lift, a certified quitting counterexample, or a more upstream general reduction. |
| `PC-002` | Treat terminal approximate existence—not uniformization—as the finite-quitting waist. | Terminal existence iff uniform payoff is production Lean. | Continue optimizing horizon-conversion constants as the main problem. | Every quitting proof/counterexample is evaluated at terminal all-behavior exploitability. | A flaw in the formal bridge or a change of model. |
| `PC-003` | The current P0 hinge is escaping-middle compactification plus a repair decoder within the zero-pinned exact-`D` grammar; the fixed-debt-descent alternative is closed — no bounded exact extension achieves a cutoff-independent decrement (see [`AnchoredRepairOrUniformDebtDescent.md`](../../ideas/PositivePlateauBoundaryClosure/AnchoredRepairOrUniformDebtDescent.md)). **Tightness is no longer an alternative**: an explicit two-player weight has optimized debt `1/8` at every cutoff with all mass escaping to a receding terminal row, so the tails are not uniformly tight and no common truncation length exists. | Two endpoint charts, packet provenance, exact finite-block holonomy, and now the full fixed-cutoff provenance lift are compact/closed. A machine-checked length fence proves that literal unbounded game length cannot live in any compact `ℕ × X` lift. | Equate compact scalar coefficients—or fixed-cutoff closure—with a compact bounded-cost executable repair relation. | Add an infinity/stopping-law chart plus a separately bounded finite decoder, or exhibit a calibrated incompatibility family. Uniform middle-length tightness is no longer an admissible route. | A simpler repair closes every plateau, or a decisive incompatibility chooses the necessary new state/route. |
| `PC-004` | Run a direct repair ladder and all-behavior counterexample CEGIS in parallel with the P0 compactness route. | Static/short repairs may close the plateau before general geometry; the conjecture is universal, so a certified barrier is decisive. | Wait for one grand positive proof before searching for refutations. | Stationary/full-set/short-word search exports exact violated inequalities to the barrier lane; the descent lane is closed within the zero-pinned grammar (see [`AnchoredRepairOrUniformDebtDescent.md`](../../ideas/PositivePlateauBoundaryClosure/AnchoredRepairOrUniformDebtDescent.md)). | One lane obtains an exhaustive certificate that subsumes the others. |
| `PC-005` | Stop abstract work on the greedy buffered-path combinatorics. | Return/exit/dead-end is already checked; the missing theorem is game-facing anchoring and decoding. | Add more topology-only variants. | E46 is mined infrastructure; work moves to relation semantics and debt. | A decoder exposes a genuinely missing abstract combinatorial premise. |
| `PC-006` | Separate internal scientific claims, attributed literature, machine truth, and intake evidence. | Diary/index-only state produced stale and conflicting claims. | Keep an ephemeral frontier as the operative handoff. | Claim files and literature result files become authoritative; proof-mining/questions/experiments are evidence only. | A demonstrated maintenance failure in the hierarchy below. |
| `PC-008` | **Deprioritize escaping-middle compactification pending the free-terminal test.** `MATH-P0-1` and `LEAN-P1-4` drop to P1 until the optimized debt over chains with a *free admissible* terminal continuation is decided. | The entire P0 hinge is downstream of "the exact-D chain grammar has a positive plateau". That premise is now known to be about the grammar: both plateau witnesses are two-player tables with equilibria, and for the surgery witness the equilibrium is machine-checked at exactly zero debt once the terminal continuation is unpinned. Compactifying the escaping middles of a family that is biased away from the object may be work on an artifact. | Continue building marked-cylinder semantics at P0 before knowing whether the plateau survives unpinning. | Escaping-middle work continues at P1 and is not abandoned; the freed capacity goes to the free-terminal calibration and the zero-mismatch-cycle question. If free-terminal debt stays positive on some weight, the compactness lane returns to P0 with a target that is informative about the game. | The free-terminal test resolving either way, or a weight exhibiting a plateau that survives unpinning. |
| `PC-009` | **Reopen the absorption-path route; retire the finite-cycle carrier.** Restore `MATH-P0-1` and `LEAN-P1-4` to P0, superseding `PC-008`'s demotion. | Finite absorbing complementary cycles are refuted as a complete carrier in every open case: a three-coordinate weight with all diagonal entries positive admits none of any length, and a case-3 weight is obstructed by an isolated negative discounted limit. What does exist is a family of absorbing cyclic recursions of period `3m` with complementarity defect of order `1/m`, converging to a continuous mass-parametrized absorption path — marked, in case 3, by the isolated-coordinate mismatch. So the correct carrier provably is not finite. | Keep pursuing completeness of a finite-cycle disjunction, or keep the absorption path deprioritised. | The path work resumes with a sharper target than before: it must carry the mass parametrization and the mark, and must supply the conversion from a defect-`ε` recursion to an `ε`-approximate solution. The pin diagnosis, and the tightness and surgery refutations built on the zero-pinned grammar, are unaffected and do **not** come back. | The attributed external theorem underlying the case-2 refutation failing an audit, or the defect-to-target conversion turning out to be unavailable. |
| `PC-007` | Keep one formalization lane active whenever source-ready mathematics exists. | Formalization catches quantifier/model errors and the backlog is substantial. | Pause Lean until a conjecture breakthrough. | Two-player quitting existence and stationary gap packaging remain active even while P0 mathematics is open. | No honest formalization-ready result remains. |

## Objective-priority queue

### Conjecture-closing mathematics

| ID | Deliverable | Prerequisites | Owner | Status / blocker | Acceptance and downstream consumer |
| --- | --- | --- | --- | --- | --- |
| `MATH-P0-1` | Prove a compactness theorem for **generalized completed chronological traces** with finite calibrated blocks dense in them, carrying exit-or-Never mass, anchors, the conditional packet, payoff, the completed stopping-obstacle hypograph, deleted-clock graphs, and debt. | `QuittingBoundaryHolonomy`, `QuittingBoundaryHolonomyCompactness`, two-ended packet, calibrated minimizer provenance. | [Realized anchored holonomy closedness](../../ideas/PositivePlateauBoundaryClosure/RealizedAnchoredHolonomyClosedness.md), [enriched absorption paths](../../ideas/PositivePlateauBoundaryClosure/EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md), [cylinder design note](design/MarkedAbsorptionCylinder.md) | `ACTIVE`, **demoted to P1 by `PC-008`** pending the free-terminal test. Finite semantics and fixed-cutoff closure are landed. Closure of the finite realized set is refuted, and no sequentially compact added coordinate can close it with continuous projection. Completed chronological graphs supply ambient compactness, a continuous cap with retained witness, closed anchored splice, and continuous concatenation. | A compactness/density theorem for the generalized trace space plus the exact finite adapter. Do **not** pursue a missing-compact-coordinate closure of the finite set; that shape is impossible. |
| `MATH-P0-2` | Prove the robust pointwise alternative: a corrected augmented-AP-to-terminal-profile compiler, within the zero-pinned exact-`D` grammar. The bounded-finite-surgery cutoff-independent-debt-descent alternative at the original root is closed (see [`AnchoredRepairOrUniformDebtDescent.md`](../../ideas/PositivePlateauBoundaryClosure/AnchoredRepairOrUniformDebtDescent.md)); uniformize the surviving repair branch by sequential compactness. | `MATH-P0-1`, corrected full-jump continuation semantics, E40, E46, E47, exact root construction. | [Anchored repair or descent](../../ideas/PositivePlateauBoundaryClosure/AnchoredRepairOrUniformDebtDescent.md), [enriched absorption paths](../../ideas/PositivePlateauBoundaryClosure/EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md) | `ACTIVE`; the abstract buffered-path trichotomy is complete, but neither game-facing decoder nor its local stability theorem is proved. | For fixed accuracy and positive debt threshold, every limit state has one stable finite repair certificate or fixed local `L_z,c_z>0`; sequential contradiction produces uniform `L,c`, terminal approximate profiles, or contradicts the plateau. |
| `MATH-P0-3` | Exhaust the inexpensive repair ladder: cutoff-one, full stationary set, quitter sets/pairs, and short accepted holonomy words. | Exact stationary caps, owner/joiner obstruction, fixed-word holonomy acceptance. | [Stationary repair](../../ideas/StationaryRepairExhaustion/README.md), [plateau repair fences](../../ideas/PositivePlateauBoundaryClosure/RepairAndClosureShortcutsAreFalse.md) | `ACTIVE` parallel lane; no finite grammar is assumed complete. | Produce an actual repair, or a uniform violated inequality consumable by `MATH-P0-2`/welfare separation. |
| `MATH-P2-1` | Turn one controlled vanishing-discount APS family into a split-domain gain--bias packet. | Stable support/domain or resolved singular scales. | [Vanishing-discount synthesis](../../ideas/VanishingDiscountResponseSynthesis/DiscountedCertificatesConvergeToGainBiasPackets.md) | `ACTIVE`, downstream; no general family producer. | Source-aligned packet consumed by semantic credibility, or a chattering counterexample fixes scope. |
| `MATH-P2-2` | Derive a strictly positive global welfare separator from robust repair failure, or refute that lift. | Global occupation polytope and local failure data. | [Positive welfare separator](../../ideas/PositiveWelfareSeparator/FailedRepairMayYieldPositiveGlobalWelfareSeparator.md) | `PENDING`; positivity/globality not supplied by local Farkas separation. | Positive Bellman bias feeds landed security/welfare assembly, or a small exact sign counterexample closes the general route. |
| `MATH-P2-3` | Route one actual analytic Bellman/value leaf through a named strategic gate or a consumed closure/obstruction alternative. | Selected target, source-aligned analytic leaf, exact support/domain. | [Analytic-leaf gate or alternative](../../ideas/AnalyticLeafRouting/AnalyticLeavesNeedGateOrAlternative.md) | `PENDING`; analytic germs can fail zero holonomy, and no universal router/target selector exists. | A concrete leaf reaches a production credibility/compiler interface, or its typed obstruction forces a proved alternative. |
| `MATH-P2-4` | Complete fixed public-controller rejection and bounded-template synthesis at each supplied size. | Public controller skeleton, reachable-arena convention, gain--bias verifier. | [Bounded public-controller synthesis](../../ideas/BoundedPublicControllerSynthesis/FixedPublicControllersAreVerifiableButNotKnownComplete.md) | `ACTIVE` P2; finite-public completeness is false, clocked-private completeness open (Q94), and no total computable public-node bound is source-conditionally available (Q98). | Fixed-`K` accept/reject certificates with exact scope; never infer all-size failure or unrestricted coverage. |

### Refutation lane

| ID | Deliverable | Prerequisites | Owner | Status / blocker | Acceptance and downstream consumer |
| --- | --- | --- | --- | --- | --- |
| `NEG-P0-1` | Certified finite quitting table with terminal exploitability gap `δ>0` against every behavioral profile. | Stopping-law semantics, terminal-to-uniform nonexistence bridge, exhaustive barrier language/rank. | [Counterexample acceptance](../../ideas/QuittingGameConjecture/CounterexampleNeedsPositiveBehavioralExploitabilityGap.md) | `ACTIVE CEGIS`; current screens exclude only subclasses. | One fixed positive all-behavior gap refutes the quitting and general conjectures. |
| `NEG-P1-1` | Exact screens combining owner joining obstruction, coalition-friction fence, and stationary gap on rational four-player tables. | E37/E39/E48-style inequalities. | Same owner plus [four-player literature fence](../../ideas/UniformEquilibriumLiterature/FourPlayerQuittingFallbacksFail.md) | `ACTIVE` experiment lane; not exhaustive. | Reject tables cheaply or feed survivors to longer behavioral/barrier search. |

### Lean formalization lane

| ID | Deliverable | Prerequisites | Owner | Status / blocker | Acceptance and consumer |
| --- | --- | --- | --- | --- | --- |
| `LEAN-P1-1` | Source-aligned six-scalar proof that every two-player quitting game has stationary terminal epsilon equilibria. | Full-rate cap, pair repair, source case split. | [Two-player theorem](../../ideas/TwoPlayerBaseCaseExhaustion/EveryTwoPlayerQuittingGameHasStationaryApproximateEquilibria.md) | `ACTIVE`; pure-case/orientation/vanishing-solo branch missing. | Target and umbrella build; terminal-to-uniform consumer; Q132 nonattainment regression. |
| `LEAN-P1-2` | Define stationary regret and formalize zero-infimum/payoff versus positive typed gap. | `QuittingFullRateStationaryVerifier`. | [Stationary gap or escape](../../ideas/StationaryRepairExhaustion/StationaryExploitabilityHasGapOrEscapeDichotomy.md) | `READY`; packaging absent. | Exact dichotomy reaches terminal selection or negative search API. |
| `LEAN-P1-3` | Package Q132's exact behavioral nonattainment table. | behavioral hazards as quit-time/Never mixtures; stopping-law expectation identity. | [Nonattainment fence](../../ideas/StationaryRepairExhaustion/NaiveStationaryCompactificationNeedNotAttainEquilibrium.md) | `PARTIAL`. Scope corrected 2026-08-04: the table, the stationary no-go, and the vanishing-error family are already production in `QuittingTerminalPacketSimpleFallbackCounterexample.lean`; the actual gap is the stationary-to-behavioral upgrade. Route settled — the stopping-law identity plus a support-argmax lemma, **not** a non-stationary generalization of the constant-root complementarity algebra. Draft in `experiments/` has the infrastructure `sorry`-free and the degenerate case closed; one `sorry` remains for reachability positivity and the finite per-atom case analysis. | Permanent regression for compactified cap/attainable-tail claims. |
| `LEAN-P1-4` | Define the finite marked absorption-cylinder encoding and prove its exact payoff, obstacle/cap, debt, packet, anchor, and concatenation identities. | Stable mathematical type from `MATH-P0-1`; existing finite exact-D and holonomy APIs. | [Enriched absorption paths](../../ideas/PositivePlateauBoundaryClosure/EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md) | `DESIGN`, **demoted to P1 by `PC-008`** pending the free-terminal test; do not scaffold the infinite topology before the finite semantic map is fixed. | Every production finite block embeds without changing its strategic meaning; basis for P0 compactness and endpoint adapters. |
| `LEAN-P2-1` | Source-aligned FTV stationary-impossibility theorem. | Recheck source epsilon quantifier. | [FTV literature result](../../ideas/UniformEquilibriumLiterature/FTVCyclicGameHasNoStationaryApproximateEquilibria.md) | `BLOCKED` on exact source statement. | Build-clean theorem reusing landed FTV table; positive cyclic regression. |

### Literature import lane

| ID | Deliverable | Owner | Status / blocker | Acceptance and consumer |
| --- | --- | --- | --- | --- |
| `LIT-P1-1` | Audit and formalize source-stable four-player fallback-collapse propositions. | [Four-player fallbacks fail](../../ideas/UniformEquilibriumLiterature/FourPlayerQuittingFallbacksFail.md) | Primary final paper located; numerical period-two packet disputed. | Qualitative fences only, exact source attribution, no uncertain constants. |
| `LIT-P1-2` | Complete FTV source statement audit. | [FTV stationary fence](../../ideas/UniformEquilibriumLiterature/FTVCyclicGameHasNoStationaryApproximateEquilibria.md) | Exact small-error quantifier needs reread. | Unlocks `LEAN-P2-1`. |
| `LIT-P1-3` | Audit the Solan--Solan Q-matrix normalization and import the non-Q ordinary-uniform theorem as a quitting preprocessor. | [Non-Q quitting games](../../ideas/UniformEquilibriumLiterature/NonQQuittingGamesHaveUniformApproximateEquilibria.md) | Preprint full text audited 2026-08-03: matrix/LCP/`Q` conventions resolved. Two scope corrections landed — the non-`Q` conclusion is a synthesis of Lemma 2.6, Lemma 2.10, and Theorem 2.11(1), and is stated stationary/undiscounted, not uniform. Residual blocker is the Solan--Vieille uniform upgrade. | Classify tables and test whether the positive-debt residual necessarily lies on the still-hard Q side. |
| `LIT-P2-1` | Define the positive-recursive nonrectangular theorem's exact repository adapter. | [2025 result](../../ideas/UniformEquilibriumLiterature/PositiveRecursiveNonrectangularGamesHaveUniformPayoffs.md) | Recorded, no consumer/interface. | Check examples and expose construction data useful to boundary repair. |
| `LIT-P2-2` | Separate source-aligned Bewley--Kohlberg inputs from the independent Puiseux route. | [MN/BK result](../../ideas/UniformEquilibriumLiterature/MertensNeymanDependsOnBewleyKohlbergSelection.md) | Singular general Shapley branch and source proof audit. | No unconditional classical theorem claim until selection, variation, and limit identification are explicit. |

### Engineering and documentation lane

| ID | Deliverable | Status / blocker | Acceptance and consumer |
| --- | --- | --- | --- |
| `ENG-P0-1` | Put CI under `.github/workflows/` and make its documented commands green. | Current `.github/ci.yml` is not discovered; placeholder and repository audits fail. | A clean clone runs build, placeholders, repository audit, and axiom audit deterministically. |
| `ENG-P0-2` | Make axiom audit exact and add P0 keeper capstones. | Multiline parser misses 10/48 outputs; prerequisite build implicit. | Requested declarations equal parsed declarations; explicit build target; quitting/uniform keepers audited. |
| `ENG-P1-1` | Classify 25 root-unreachable Lean modules and `opaque/native_decide` policy. | Stable library, regression, certificate, and research surfaces currently mixed. | Every module has an intentional target/import surface; policy exceptions are explicit. |
| `ENG-P1-2` | Keep this pipeline/frontier and claim-level venue link-clean and current. | Migration in progress; ignored intake has stale links. | Cold-handoff check passes; no durable status depends only on ignored files. |

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
- Arbitrary behavioral quitting deviations became mixtures of deterministic
  quit times and Never, closing a major strategy-class interface.
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
- Uniform middle-length tightness was refuted by an explicit two-player
  weight with optimized debt `1/8` at every cutoff and all mass escaping to a
  receding terminal row (`PC-003`); bounded exact-extension descent was then
  refuted as a cutoff-independent root-debt decrement (`972ba5e`); and both
  known positive-debt plateaus were shown to be manufactured by pinning the
  terminal continuation to zero -- both witnesses are two-player tables with
  exact zero-debt equilibria once unpinned, and both equilibria are
  machine-checked (`3b04928`).

## Handoff maintenance

Before handoff, update the audited commit, uncommitted-work warning, active
blockers, and any PC decision changed by new evidence. A theorem/refutation
commit updates its exact claim file; a changed mathematical boundary also
updates `FRONTIER.md` in the same stable point or an immediately following doc
commit. A priority/route change gets a PC row here. Formalized status requires
an exact declaration/path and successful check; published status requires
source attribution and a scope adapter.
