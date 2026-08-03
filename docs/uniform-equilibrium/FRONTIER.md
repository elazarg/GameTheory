# Uniform-equilibrium mathematical frontier

**Curated at commit `14d75ff`, 2026-08-03.** Production Lean is machine truth;
checked experiments and uncommitted files are labelled separately and do not
become landed by appearing here.

## Conjecture and semantic waist

For every finite stochastic game, initial state, and accuracy `ε>0`, the
uniform-equilibrium conjecture asks for a behavioral profile and fixed target
payoff `v` such that one profile both delivers `v` and caps every unilateral
behavioral deviation for every sufficiently long finite horizon. The profile
may depend on `ε`; the target is fixed. Public finite memory, private memory,
clock dependence, and unrestricted behavior are distinct strategy classes.

Production `Uniform.lean` states the semantic predicate and its equivalent
quantitative deviation-cap constructor. The general existence theorem remains
the repository's one intentional open declaration. Verification of a supplied
certificate, synthesis in a bounded class, and coverage of all semantic
equilibria are separate claims.

Payoff terminology is fixed in
[`Stochastic/README.md`](../../GameTheory/Concepts/Stochastic/README.md):
limiting-average, undiscounted-limit, and uniform finite-horizon notions are
not interchangeable without a named upgrade theorem.

## Established dependency chain for finite quitting games

The finite-quitting front is now sharply reduced.

1. **Terminal waist (`M+L+C`).** Terminal approximate Nash profiles for every
   accuracy exist iff a uniform-equilibrium payoff exists. See
   [the exact claim](../../ideas/QuittingGameConjecture/TerminalApproximateExistenceIffUniformPayoff.md),
   `QuittingTerminalUniformization.lean`, and
   `QuittingTerminalUniformPayoffSelection.lean`.
2. **All behavioral deviations (`M+L`).** Against fixed opponents, a quitting
   deviation is exactly a mixture of deterministic quit times and Never. The
   live-history hazard sequence preserves terminal payoff and unilateral
   deviation values.
3. **Finite exact chain optimization (`M+L+A`).** Exact zero-boundary Nash--
   Bellman chains are compact at each cutoff; optimized aggregate dynamic debt
   is attained and nonincreasing. See
   [the optimized split](../../ideas/QuittingGameConjecture/OptimizedDebtSplitIsExhaustive.md).
4. **Zero branch (`M+L+C`).** If optimized debt tends to zero, selected chains
   give terminal approximate equilibria and therefore a uniform payoff.
5. **Positive branch (`M+L+A`).** A positive limit selects one owner, a forward
   exact-D tail with summable opponent clock, and a nonvanishing full terminal
   action packet. The owner-own-hazard split is exhaustive; its divergent branch
   closes, leaving only the fully summable boundary. See
   [the packet claim](../../ideas/PositivePlateauBoundaryClosure/PositiveDebtProducesAnchoredTerminalPacket.md).
6. **Two endpoint charts (`M+L`).** Reading the same minimizers from both ends
   gives a forward positive-debt ray and a reverse ray ending on the terminal
   face with a quantitative depth-one packet. The middle length still diverges.
7. **Finite middle algebra (`M+L`, `e1fe7dc`).** Every actual finite middle has
   an associative multiplayer `QuittingBoundaryHolonomy` with exact prescribed
   `(B,P)` and arbitrary-behavior `(A,T,χ)` semantics, source roots, exact-D
   endpoints, and packet provenance. Fixed-word cap safety is affine.
8. **Fixed-cutoff topology and the length fence (`M+L`, `14d75ff`).** For each
   cutoff, the resolved graph retaining the complete source path and all legal
   subblock holonomies is compact and closed. The fixed-last calibrated lift
   is finite and retains the selected minimizer, owner, marked action,
   exact-D endpoints, survival, atom, and common holonomy. Conversely, every
   compact subset of `ℕ × X` has bounded length, so no compact lift retaining
   literal unbounded game-stage cost can cover the escaping middles.
9. **Leading infinity-chart candidate (`P+I`).** Published absorption paths
   compactify quitting behavior by accumulated absorption mass rather than
   calendar time.  The P0 candidate is stricter: a marked subprobability path
   with a finite-block exit port or infinite Never atom, the conditional
   terminal packet, entry/exit anchors, payoff/debt paths, and the full
   unilateral stopping-obstacle graph.  Neither its closedness nor its exact
   adapter is proved.

The chain is exhaustive up to the positive fully summable plateau. It is not a
claim that every equilibrium belongs to one finite grammar.

## Exact open hinge

Fixed-cutoff closedness is settled; arbitrary-length executability is not.
Projection to scalar coefficients forgets splice admissibility, while a state
retaining literal finite length cannot remain a complete finite-realizability
certificate after compact closure.  Boundary objects representing an escaped
infinite or continuous middle are unavoidable unless plateau middles are
uniformly tight.  The leading candidate is therefore the
[marked absorption-path route](../../ideas/PositivePlateauBoundaryClosure/EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md), with the
[escaping-middle problem](../../ideas/PositivePlateauBoundaryClosure/RealizedAnchoredHolonomyClosedness.md)
retained as its acceptance/falsification test.  The first theorem must encode
actual finite blocks exactly; the next must prove the enriched strategic graph
closed or exhibit two identical ordinary path limits with incompatible caps,
marks, or splice semantics.

The second question is strategic and splits into two decoders.  One compiles a
globally valid corrected path into terminal approximate profiles.  The other
extracts a bounded finite surgery from a strict local failure and decreases
optimized debt at the original root.  E40 gives depth-free error once a certified
seam is supplied; E46 gives a greedy buffered return/exit/dead-end trichotomy;
E47 applies a downstream seam to the actual exact-D tail. None transports the
root anchor and reverse packet through the middle or turns an exit into new
exact roots with a cutoff-independent debt decrement. The required capstone is
[anchored repair or uniform debt descent](../../ideas/PositivePlateauBoundaryClosure/AnchoredRepairOrUniformDebtDescent.md).

A positive solution yields terminal approximate existence. A fixed bounded
decrement contradicts the positive plateau. A counterexample to this producer
would redirect the construction but would not alone refute equilibrium
existence.

## What the quitting front would—and would not—settle

No reduction from arbitrary finite stochastic games to finite quitting games
is known. The current quitting decomposition is exhaustive **inside the
quitting model**; it is not an induction or normal form for general stochastic
games.

- A positive solution would prove the uniform-equilibrium conjecture for every
  finite quitting game. It would likely export reusable stopping-law,
  credibility, and boundary-repair mechanisms, but it would not by itself
  settle general finite stochastic games.
- One finite quitting table with a fixed positive all-behavior terminal
  exploitability gap would refute both the quitting conjecture and the general
  universal conjecture.
- After a positive quitting solution, the general proof would still need an
  endogenous target/continuation selector, a strategically credible response
  producer beyond the one-live-state geometry, and a bridge across the public
  finite, clocked/private, and unrestricted strategy classes. Manufacturing
  ordinary-play correlation remains a separate interface; correlated
  existence does not supply it.

Thus quitting games are the right direct P0 test bed and the complete negative
front, but not an invented reduction backbone.

## Serious parallel routes

- **Repair ladder.** Exact full-rate stationary caps, owner-solo certification,
  pair repair, quitter-set tests, contracting periodic compilers, and fixed-word
  holonomy acceptance can find a short repair before general compactness. See
  [stationary repair](../../ideas/StationaryRepairExhaustion/README.md). Failure
  of a narrow grammar does not imply nonstationarity.
- **Positive separator.** Failed repair might yield strictly positive welfare
  weights and a global Bellman bias. The downstream security/welfare assembly
  is landed; positivity and globality are open. See
  [the separator claim](../../ideas/PositiveWelfareSeparator/FailedRepairMayYieldPositiveGlobalWelfareSeparator.md).
- **Vanishing discount.** A controlled discounted APS family might converge to
  a split-domain gain--bias packet. Support and singular-scale stability are
  open. See [the exact conjecture](../../ideas/VanishingDiscountResponseSynthesis/DiscountedCertificatesConvergeToGainBiasPackets.md).
- **Analytic leaves.** Actual Bellman/Puiseux leaves may feed a response
  architecture only through a proved gate-or-alternative theorem. Analyticity
  alone does not imply ownership, zero holonomy, or credibility. See
  [the exact routing claim](../../ideas/AnalyticLeafRouting/AnalyticLeavesNeedGateOrAlternative.md).
- **Bounded public controllers.** A supplied finite public architecture is
  finitely verifiable and fixed-size synthesis is meaningful. Finite-public
  completeness is false, clocked-private completeness is open, and the
  source-conditional Q98 boundary supplies no total computable node bound.
  See [the scoped claim](../../ideas/BoundedPublicControllerSynthesis/FixedPublicControllersAreVerifiableButNotKnownComplete.md).
- **Refutation.** A finite quitting counterexample must have one positive
  terminal exploitability gap against **all** behavioral profiles. Stationary,
  First, finite-period, or bounded-atlas exclusions are only screens. See
  [the acceptance criterion](../../ideas/QuittingGameConjecture/CounterexampleNeedsPositiveBehavioralExploitabilityGap.md).

## Quantitative and certificate-complexity metadata

These facts calibrate theorem scope; they do not reorder the P0 queue.

- FTV's landed architecture has the exact coordinate delivery constants
  `16/7`, `22/7`, `18/7` and common finite-horizon modulus `22/(7T)`.
- `QuittingPeriodicFiniteHorizonRate.lean` proves a conditional mesh compiler:
  terminal charge `A/m` plus boundary charge `B m/N`, with
  `sqrt N <= m <= 2 sqrt N`, gives an explicit `O(N^{-1/2})` Nash bound. It is
  not a universal producer of the required certificate family.
- Fixed controller skeletons/support cells yield finite LP or semialgebraic
  verification problems. Complexity depends on controller size, recursion
  depth, branching, polynomial degree, input bit size, and accuracy—not only
  on the game state count.
- Q98's no-computable-public-node-bound conclusion is source-conditional and
  not Lean-formalized. It fences unbounded synthesis; it does not make fixed
  templates unverifiable. Q94 leaves clocked-private completeness open.

## Known positive islands and published boundaries

The attributed literature ledger is
[`UniformEquilibriumLiterature`](../../ideas/UniformEquilibriumLiterature/README.md).
Key boundaries are:

- finite two-player zero-sum stochastic games have a uniform value (Mertens--
  Neyman, consuming Bewley--Kohlberg); the repository has a substantial
  conditional/independent algebraic route, not yet the full classical theorem;
- two-player non-zero-sum stochastic games are settled (Vieille 2000), and
  two-player/three-player absorbing subclasses are settled;
- autonomous correlated equilibrium exists for every finite player number,
  but the device uses private contingent recommendations and delayed
  disclosure—not merely a public coin. No de-correlation theorem closes
  ordinary Nash;
- positive-recursive nonrectangular one-live-state absorbing games have a
  uniform payoff in the 2025 preprint at its exact stated scope;
- the FTV three-player game proves stationary incompleteness while supplying a
  cyclic uniform equilibrium; much of its positive architecture/delivery is
  already in Lean;
- Solan--Vieille's four-player table destroys the standard stationary,
  perturbed, small-termination, and solo-hull fallback conclusions. Its
  qualitative fence is source-stable; the printed period-two numerical packet
  remains disputed; and
- Renault's precompact directed non-expansive criterion is a one-player dynamic
  programming theorem and possible lift/failure interface, not a multiplayer
  Nash theorem.

## Formalization status at the frontier

| Object | Evidence | Exact status |
| --- | --- | --- |
| General semantic waist and deviation-cap equivalence | `L` | Landed; general existence intentionally open. |
| Finite-quitting terminal-to-uniform equivalence | `M+L+C` | Landed and consumed. |
| Quit-time/Never extremality for behavioral deviations | `M+L` | Landed. |
| Exact-D optimizer and zero/positive split | `M+L+A+C` on zero branch | Landed. |
| Owner clock/packet and two-ended core | `M+L+A` | Landed; stronger preselected-mark bridge products remain mathematical/experimental. |
| Finite-block boundary holonomy | `M+L` | Landed at `e1fe7dc`. |
| Fixed-cutoff resolved holonomy graph | `M+L` | Compact/closed with full source path; fixed-last calibrated lift finite, in `QuittingBoundaryHolonomyCompactness.lean` at `14d75ff`. |
| Greedy return/exit/dead-end | `M+X` | Checked experiment, natural abstract stopping point; not production/decoder. |
| Realized arbitrary-length holonomy/decoder | `M+L/I` | Fixed-cutoff case landed; literal unbounded-length compact lift ruled out. Tightness or an infinity/stopping-law chart plus bounded decoder remains open. |
| Anchored seam/exit strategic decoder | `I` | Open. |
| Full-rate stationary cap | `M+L+C` | Landed verifier for supplied profiles. |
| Two-player all-table stationary approximate producer | external `M`, internal partial `L` | Source case split not fully formalized. |

## Decisive falsifiers and prohibited claims

- Big Match: Markov/fixed public-memory completeness is false.
- FTV: stationary equilibrium is not the root strategy class.
- Four-player fallback fence: the `n<=3` consolation alternatives do not
  propagate.
- Q125: positive zero-boundary chain debt does not imply nonexistence; another
  stationary payoff can lie outside that chain geometry.
- Q129: atomwise regret does not transfer debt ownership.
- Q132: attainable payoff/cap data and actual stationary regret can be
  nonclosed; a relaxed zero need not be an exact equilibrium.
- E50: two endpoint limits from common finite chains do not automatically form
  a bi-infinite orbit or share an anchor-persistent segment.
- Chain recurrence alone does not concentrate all pseudo-orbit error into one
  exact seam; pointwise debt decrease need not have a uniform decrement.
- Monitoring/evidence cannot by itself make costly punishment credible.
- Correlated existence does not mean ordinary existence reduces to a public
  lottery.

Accordingly, the project cannot currently claim a quitting-game solution, a
general induction backbone, finite-architecture completeness, realized
holonomy closedness, or a counterexample.

## What counts as resolution

**Positive quitting solution:** a theorem covering the positive plateau and
feeding terminal approximate existence for every accuracy, then the landed
terminal-to-uniform consumer.

**Counterexample:** one explicit finite table and fixed `δ>0` proving every
behavioral profile has a unilateral terminal gain at least `δ`, followed by the
landed nonexistence transfer.

**Meaningful intermediate resolution:** either a closed/exhaustive anchored
holonomy relation with a correct decoder; a decisive nonclosedness theorem
identifying the necessary extra state; a universal short-repair theorem for a
substantial class; or a typed positive stationary/all-word gap that materially
shrinks counterexample search without being mislabeled global.

For long-form intuition, examples, glossary, and theorem/module map, see the
[research atlas manuscript](manuscript/UniformEquilibriumFrontierManuscript.tex).
It is derivative exposition, not status authority.
