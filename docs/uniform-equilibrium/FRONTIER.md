# Uniform-equilibrium mathematical frontier

**Curated at commit `14d75ff`, 2026-08-03; prose updated through `52aabd3`,
2026-08-05.** Session IX capstone wave: the punishment-floor/feasible-set
paragraph (edited stale before both landed) is corrected, the two-player
capstone and its no-exact-stationary-equilibrium negative are recorded, and
the minimality corollary is fixed. Production Lean is machine truth; checked
experiments and uncommitted files are labelled separately and do not become
landed by appearing here.

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
9. **Infinity chart: generalized completed traces (`M [reported]`).** Published
   absorption paths compactify quitting behavior by accumulated absorption
   mass rather than calendar time. For the stricter marked object, closure of
   the *finite* realized set fails, and fails structurally. The unilateral
   stopping obstacle is not a function of accumulated mass — equal accumulated
   mass does not determine the current row (`M`, machine-checked:
   `QuittingObstacleMassDescentCounterexample.not_exists_obstacle_as_function_of_accumulatedMass`)
   — and neither are the deleted clocks after full absorption. Finite
   `μ`-paths are finitely piecewise affine while limits are genuinely
   nonlinear. Decisively, **no sequentially compact added coordinate closes
   the finite realized set with continuous projection**, so a
   missing-coordinate repair of that shape does not exist.

   A candidate repair — completed chronological graphs, closing on the joint
   vector-factor trace plus obstacle hypographs — is claimed compact and
   determining, with finite complementary arrays dense and pulling back in
   trace, cap, and origin value simultaneously. **This is an unaudited,
   unformalized solver's answer, not a landed result**; see
   [`CompletedVectorFactorTraceIsCompactAndDetermining.md`](../../ideas/PositivePlateauBoundaryClosure/CompletedVectorFactorTraceIsCompactAndDetermining.md)
   for the exact statement, scope, and what would raise its seal. The claimed
   aggregated-carrier fallback failure (fibres carrying different origin
   values at the same obstacle trace) is likewise `M [reported]`; see
   [`AggregatedCarrierConflatesOriginValues.md`](../../ideas/PositivePlateauBoundaryClosure/AggregatedCarrierConflatesOriginValues.md).
   The exact finite adapter remains unproved regardless.

The chain is exhaustive up to the positive fully summable plateau. It is not a
claim that every equilibrium belongs to one finite grammar.

## Exact open hinge

**Uniform middle-length tightness is refuted (`M`).** An explicit two-player
weight — `r({1})=(1/4,0)`, `r({2})=(1,-1/4)`, `r({1,2})=(3/4,1/4)` — has
optimized debt `1/8` at every cutoff with unique complementary minimizers and
total absorption mass `3/4`. The minimizer's only positive-mass row is the
*last* one, so for every window length `L` the mass beyond `L` remains `3/4`
and the tails are not uniformly tight. The escaping structure is therefore
explicit: a bounded terminal packet carrying positive deleted hazard and
boundary debt, preceded by an arbitrarily long **inert** region of zero
absorption mass and zero deleted clock.

This closes the first horn of `PC-003`'s revisit trigger negatively — no
common finite truncation length exists, so the bounded-decoder route via
tightness is unavailable, and an infinity/stopping-law chart is mandatory
rather than merely preferred. It also supplies the missing witness for the
chart's design: the inert middle collapses to a single point of the mass
clock, so everything strategic sits at a receding row that mass alone cannot
locate — exactly the failure of mass-parametrization recorded in item 9.

A positive plateau in this chain grammar does **not** imply nonexistence; by
the Q125 fence an equilibrium may lie outside the zero-boundary chain
geometry, and for two players one is guaranteed externally.

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

The second question is strategic and splits into two decoders. One compiles a
globally valid corrected path into terminal approximate profiles. The other
extracts a bounded finite surgery from a strict local failure and decreases
optimized debt at the original root.

**The surgery decoder is closed negatively (`M`)** — see the capstone claim.
No bounded-length modification achieves a cutoff-independent decrement, and
accumulation does not rescue it. Within this grammar, repair is the only
surviving branch.

**But the plateau driving that closure is manufactured by the zero pin (`M`).**
Both known plateau witnesses are two-player tables that have exact equilibria
with debt zero once the terminal continuation is unpinned, and both equilibria
are machine-checked: player one mixes at rate `1/2`, player two never quits,
values `(a,0)` and `(1/4,0)` respectively, with both coordinates exactly
indifferent and absorption rate `1/2`. The pin forces a strictly positive gap
at every finite horizon, which forces the opponent survival product below one,
which creates the debt; let the gap go to zero and the plateau vanishes.

So "repair is the only surviving branch" is a fact about the exact-`D`
zero-boundary grammar, **not** a demonstrated requirement of the program. A
positive plateau in that grammar is evidence the grammar missed the
equilibrium. Do not read the descent closure as urgency to find a repair for
the games; read it as a reason to fix the carrier. `PC-008` accordingly
deprioritizes escaping-middle compactification pending the free-terminal test.

**The replacement carrier (`M`, partial).** Instead of a finite chain with an
inert zero tail, take a **cycle**: rows `y_1,…,y_L` and values `z_1,…,z_L` with
`z_k = F_{y_k}(z_{k+1})` cyclically, each `(y_k, z_{k+1})` complementary, and
`∏_k c(y_k) < 1`. Absorption is load-bearing — without it the all-continue list
reproduces *every* value vector and the notion is vacuous, and the same trap
appears at the level of single rows, where the all-continue row is exact
endpoint-Nash against both plateau tables' equilibrium values.

Two results are in hand. Define the mismatch against the anchor
`ẑ_i := lim_N T_i^N(Λ_i)`, where `T_i` is the cyclic composite of the phase maps
`w ↦ max{Σ_i, A_i + c_{-i} w}` — the anchor carries the content, since
anchoring at the cycle's own value makes the mismatch identically zero, and in
the isolated case `T_i` has a continuum of fixed points. Then: `T_i` is
`P_i`-Lipschitz with `P_i = ∏_k c_{-i}(y_k)` and fixes the cycle's value, so the
mismatch is zero whenever `P_i < 1`, for either sign of the terminal gap. It is
nonzero only when `P_i = 1` — every opponent of `i` silent at every phase, the
*isolated* configuration, of which an absorbing cycle admits at most one — and
`r_i({i}) < 0`, in which case it is exactly `-r_i({i})`. And a
length-one admissible cycle exists whenever some `i` with `r_i({i}) > 0` admits
a rate `p ∈ (0,1]` with `(1-p)·r_j({j}) + p·r_j({i,j}) ≤ r_j({i})` for every
`j ≠ i` — the classical no-join condition, here in exact cycle form, affine in
`p` and hence one-dimensionally decidable. Both plateau tables satisfy it at
exactly `p = 1/2`.

**The conditional is closed (`M+L`).** An admissible absorbing cycle — one in
which every coordinate has either deleted survival product below one around the
cycle, or nonnegative solo weight — yields a periodic profile that is terminal
`0`-Nash at every phase, hence terminal `ε`-Nash at every accuracy, hence a
uniform equilibrium payoff through the landed selection theorem. There is **no
strategy-class gap**: the consumed predicate quantifies over all behavior
strategies.

**Nor is there a surrogate gap (`L`).** The terminal payoff is not a stand-in
for the asymptotic one: `tendsto_finiteAveragePayoff_quittingGame` gives
convergence of the finite average to `quittingTerminalPayoff`
**unconditionally, for every profile, including off-path deviations**. So exact
terminal Nash *is* exact `0`-equilibrium of the asymptotic-payoff game, and per
stage the Nash–Bellman edge condition is equivalent to full one-shot mixed Nash.
An absorbing cyclic continuation block is therefore the same object as the
literature's finite-period completely absorbing admissible sequence — the
comparison with published non-existence theorems is sound, not an equivocation.

The admissibility hypothesis is not removable; a one-stage block
with negative solo weight, its owner quitting at rate `1/2` against a silent
opponent, satisfies every other clause while the owner gains by continuing
forever.

**Consequently the finite-quitting conjecture reduces to one statement — but
not the naive one.** "Every weight admits an admissible absorbing cycle" is
**false** (`M`): for `r({1})=(0,-1)`, `r({2})=(1,-1)`, `r({1,2})=(0,0)` every
discounted complementary row vanishes, and every absorbing complementary cycle
either isolates coordinate `2`, whose solo weight is `-1`, or contradicts
complementarity at coordinate `2`. The corrected reduction is:

> For every weight, either `Λ = 0` — and the landed zero branch applies — or
> the weight admits an admissible absorbing cycle **of some finite length**.

**The implication is one machine-checked theorem** (`M+L`),
`exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle`: either branch
yields a uniform equilibrium payoff, the zero-solo branch delivering the named
payoff `0`.

**That two-branch disjunction is machine-checked false** and has been replaced.
`not_isQuittingZeroSolo_reward` and `not_hasAdmissibleAbsorbingQuittingCycle_reward`
refute it on a single two-coordinate weight. The repaired statement is the
trichotomy `quittingCycle_zeroSolo_or_admissible_or_isolatedNegative`, adding a
third *isolated-negative* branch — a genuine absorbing cycle in which some
coordinate is isolated with negative solo weight, so its mismatch is exactly
`-r_i({i})` and admissibility fails without absorption degenerating.

The trichotomy leaves **two holes**, and these are the open content:

1. It is exhaustive only under the hypothesis that the weight admits an
   absorbing complementary cycle **at all**. Weights admitting none of any
   period are outside it entirely. **This hole is occupied, and the occupancy
   is machine-checked end to end (`L`)**: for every `ε ∈ (0, 2]`,
   `¬∃ terminal, IsQuittingCyclicContinuation (ftvRewardEps ε) terminal` —
   the trichotomy's own predicate — via the label lock in the real encoding
   (all periods, with the `ε = 0` rotation as the in-file boundary witness)
   and the cycle-level transport with entry-for-entry weight alignment
   (`PerturbedCyclicWeightNoExactCycle.lean`,
   `PerturbedCyclicWeightCycleExistenceHoleOccupied.lean`). The leading hard
   candidate provably lies *outside the trichotomy*; the cycle route's
   incompleteness is an internal theorem, and the published Theorem 2.1 is
   independent confirmation only.
2. The isolated-negative branch has **no sufficiency theorem**. One specific
   two-coordinate weight in it does have a uniform equilibrium payoff, by an
   explicit symmetric contracting perturbation, but that construction is stated
   not to generalize.

No bound on the length is required: the formalized conditional quantifies over
the period with no bound, so earlier statements asking for `L(n)` were stronger
than necessary. The zero-solo branch is moreover an iff, so its hypothesis
cannot be weakened.

The counterexample has `Λ = 0`, so it lies in the already-solved disjunct: its
exact equilibrium is the all-continue profile with payoff `(0,0)`, which no
coordinate can improve on. The lesson is that the absorption fence, required to
keep the cycle notion from being vacuous, also excludes the genuinely
**non-absorbing** equilibria — and those are exactly the `Λ = 0` weights, which
the matched-boundary argument already handles.

Everything else on that path is machine-checked. The open disjunct splits
exhaustively by the sign pattern of the diagonal, with `S₊ = {i : r_i({i}) > 0}`
and `S₋ = {i : r_i({i}) < 0}`:

1. **`S₊ = ∅`** — settled; this is the `Λ = 0` disjunct above.
2. **`S₊ ≠ ∅`, `S₋ = ∅`** — admissibility is *automatic*, since a mismatch can
   be nonzero only at an isolated coordinate with negative solo weight and
   there are none. So every absorbing cycle is admissible and the sole
   obstruction is absorption degenerating. **This is where the published cyclic
   three-player table lives** — all its solo weights are positive — so for the
   leading hard candidate only existence is at issue.
3. **`S₊ ≠ ∅`, `S₋ ≠ ∅`** — a second failure mode. An absorbing discounted
   limit that isolates a coordinate of `S₋` is necessarily the solo row `p·e_i`
   with value `r_i({i}) < 0`: a genuine absorbing cycle that is not admissible.
   The dichotomy then supplies nothing even though absorption did not
   degenerate, and one must argue about the whole supply of cycles rather than
   the selected limit.

Cases 2 and 3 are the remaining content. See
[the carrier group](../../ideas/AbsorbingCycleCarrier/README.md).

**Vanishing absorption is now a finite check (`M [reported]`).** Case 2 reduces
to whether absorption can degenerate, and that question has an answer in terms
of the table alone. With `dᵢ = rᵢ({i})` and `Bᵢⱼ = rᵢ({j}) - dᵢ`, consider the
normalized singleton linear complementarity problem

> `λ ∈ Δ(I)`,  `q = Bλ ≥ 0`,  `λᵢqᵢ = 0`.

Then `ε`-complementary cycles at small `ε` have absorption bounded below **iff**
this LCP is infeasible; and when it *is* feasible, period **one** already
suffices, so a diverging period is impossible. Vanishing absorption and
diverging period are therefore mutually exclusive regimes, separated by a
decidable property of the weight rather than by a limit to be estimated. This is
the same singleton LCP the residual-class group studies.

**Exact cycles are not limits of relaxed ones (`M [reported]`).** A rational
three-coordinate cyclic weight has `ε`-complementary cycles at every tolerance,
of period `3m`, and no exactly complementary cycle of any finite period. So any
route that manufactures an exact cycle as a limit of relaxed ones is closed in
general. Absorbed mass along those cycles is constantly `7/8`, so the
obstruction is not a block too mass-poor to close.

That weight is **zero-solo**, so it sits in case 1 and says nothing about
completeness — it closes a proof strategy, not a branch. The question that would
bear on completeness is whether a positive-solo weight can fail to admit an
admissible absorbing cycle; a published perturbation of the cyclic table, which
has a uniform equilibrium payoff but provably no exact equilibrium, is the
current candidate and is under test.

**Mark transport is not the obstruction (`M`).** The long-standing worry that a
packet sitting arbitrarily deep in the middle cannot be carried through a
shortening is false. Splitting at the marked letter yields mark preservation
with `L_C(ε) ≤ 2 L_B(ε/5) + 1`; there is no separate deep-mark obstruction, and
the transported weight staying bounded below is not the difficulty either.

The hypothesis must travel with the claim: the collapse needs endpoint-
preserving shortening for **every admissible factor** with exact endpoints,
which is strictly stronger than shortening whole words, since the two factors
carry endpoint pairs the full family need not contain. If the repository's
factor fibers are not covered, the collapse does not fire.

What actually fails is plain **anchored** shortening: exact reachable endpoint
fibers can have unbounded depth, and this persists even for a compact letter
set with continuous, injective, locally open anchor maps and uniformly summable
defects — so injectivity and local openness are not the missing hypotheses. A
finite anchor space, or a bounded-deletion property giving `L(ε) ≤ N(ε/4)+D`,
restores it. The open question is whether the exact-`D` anchors admit such a
condition, since they live in a compact box rather than a finite set. A common
total mass bound is insufficient throughout: prefix shortening needs a common
**tail modulus**.

The coupled version has since been asked and answered (`M [reported]`, not
audited or formalized here), and the failure is claimed **real, not an
artifact of uncoupled anchors**: with the anchor determined by the letter
data, both exact-endpoint shortening and uniform approximate shortening fail,
via a mechanism where a determined anchor pins the common continue factor
`c(y)` but not an individual deleted factor `c_{-i}(y)`. See
[`AnchoredShorteningFailsUnderDeterminedAnchors.md`](../../ideas/PositivePlateauBoundaryClosure/AnchoredShorteningFailsUnderDeterminedAnchors.md)
for the exact statement, the two counterexample weights, and what would raise
its seal. E40 gives depth-free error once a certified
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

**And "exhaustive inside the quitting model" is narrower than it reads (`M`).**
The optimized-debt split is exhaustive as a *numerical* dichotomy over one chain
class — zero-boundary exact-`D` chains — and its own claim file says so: it is
"not an exhaustive grammar of the repair" and "can omit a valid stationary
repair". It is not exhaustive over equilibrium-profile **shapes**.

A concrete family falls through every split the program has. An *instant*
approximate equilibrium — Simon 2007's notion (his "instant equilibria", one of
the three clauses of his Theorem 3): some coordinate quits with certainty at
the first stage, and is punished to its min-max value plus `ε` if it reneges — is
excluded by the stationary ladder (which forbids history-dependence outright),
excluded by the absorbing-cycle carrier (whose admissibility discriminator is a
no-join condition on opponents, not a threat aimed at the quitter, so the
period-one solo-quitter row is verified only against a *passive* continuation),
and untouched by the plateau and optimized-debt splits, which are on-path
finite-chain algebra.

The gap is structural, not a missing case, and it has now narrowed to a single
item: **no file in the quitting apparatus has a predicate for behaviour that
differs at stage two depending on stage-one history.** Stationary rows, cyclic
row-sequences, and zero-pinned finite chains have no off-path branch anywhere.
That trigger shape is the remaining obstruction.

**The punishment target is no longer inexpressible (`L`).** An earlier sweep
found no min-max or punishment construction anywhere, and that verdict is now
falsified: `PunishmentLevel.lean` supplies a finite-horizon min-max level,
individual rationality in exact and approximate form, and the necessary
condition that a uniform equilibrium payoff is eventually approximately
individually rational. The `χ` in the older quitting files remains an unrelated
best-response-summary coefficient — a name collision, not a punishment notion.

The folk bill is now two-thirds closed, superseding the previous paragraph
here. **The floor landed** (`QuittingPunishmentFloor.lean`): the naive floor
refuted first, the unconditional floor `max{(T−1)/T·mIn, mOut}`, the
sandwich converging to `max 0 (solo)` under two finitely-checkable table
conditions, exactness on the hostile witness — and **the no-go generator
refutes for the first time**: the zero payoff is not a uniform equilibrium
payoff of the quit-bonus table, margin `1/4` from horizon `4`. **The
feasible set landed** (`Feasible.lean`): finite-horizon and asymptotic,
composed with IR into the full necessary direction, with the non-convexity
fence (`(p−q)² = −1`) proving the classical folk hypothesis shape false for
this model at horizon one. What remains of the bill: the sufficiency
direction is not even conjectured in Lean, and its three named blockers are
punishment attainment below the ceiling (Q162), hull attainability (the
model lacks public randomization — and note the padding separation proves
padding *smuggles it in*: the XOR lottery attains a non-product point, so
padding strictly enlarges the feasible set, not merely the equilibrium set),
and feeding an all-errors family from the compiler into the landed selection
theorem. The capping theorem for the planned-survival stopping index arrived
with the phase-switch engine, its caps as named hypotheses.

**And the first capstone exists**: every two-player quitting game has a
uniform equilibrium payoff — `quittingGame_exists_uniformEquilibriumPayoff_twoPlayer`,
zero hypotheses, four branches, no discount limit. Known mathematics since
Vrieze–Thuijsman, but the first machine-checked existence theorem for a
nontrivial stochastic-game class, and its route is the branch classification
aimed at `n ≥ 3`, not the classical vanishing-discount argument.

The general semantic layer does not *forbid* such a profile — `IsUniformEquilibriumPayoff`
quantifies over arbitrary behaviour — so this is a gap in the decompositions,
not in the conjecture's statement.

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
| Sure-exit-set exact characterization (all `n`) | `M+L` | Landed (`QuittingSureExitSet`, `97b77b6`); coalition-face per-phase criterion is now a theorem; two-player joint exit recovered as instance. |
| Two-blocker interval-cover gate | `M+L` | Landed (`QuittingBlockerIntervalCover`, `97b77b6`); single-blocker designation refuted by table witness; with ≤ 2 opponents the switching branch is vacuous, so `n = 3` is the exact threshold. |
| Switching-residue regression and scalar obstructions | `M+L` | Landed (`QuittingSwitchingResidueRegression`, `97b77b6`); the fixed-blocker weight-level branch map is provably not total. |
| Collision-repair exact characterization (owner indifference, spectator no-join, blocker-floor balance) | `M+L` | Landed (`QuittingCollisionRepairCharacterization`, `34fdc11`): full iff, both legs, arbitrary `n` with every non-owner non-blocker a spectator; forced rate δ ≥ γ/(γ+p); sub-floor mechanism failure below γ/(4M); at rate 1 collapses to the sure-exit test. |
| Stationary min-max: `χ = inf_y Φ(y)`, both legs, full history-dependent generality | `M+L` | Landed (`QuittingStationaryMinMax`, `0829959`); constant-row cap supplies phase-switch hypothesis (P) at `punishCap = Φ(y)`; solo-clipped ceiling proved STRICTLY loose (`χ = 0` vs ceiling `2` witness); attainment and the finite-horizon `punishmentLevel` bridge deliberately unclaimed. |
| Budget-to-go / bounded-potential exact duality (abstract charged relations) | `M+L` | Landed (`Math/ChargedPathBudget` + counterexamples, `0829959`); strong duality attained, Bellman least-supersolution, positive-cycle filter; towers (uniform bound essential — pointwise finiteness insufficient), continuous incompleteness fully proved, quit-bonus `q = 1/2` self-loop calibration machine-checked. |
| `SwitchRepair` two-scale producer (switching cover → relaxed orbit) | `M [reported]`, REFUTED | Q166 answer: the no-resurrection theorem — occupation charge enters no pointwise packet clause, so vanishing-error packet families (rates bounded below) reduce to exact one-stage repairs or sure-pair sets; the producer cannot exist in the sure-blocker grammar. |
| Two-owner root (support-enlarged one-stage mechanism: sure blocker, both others mix) | `M [reported]` | Q166 Theorem C.1: explicit rational indifference rates + blocker quit-now inequality + floors ⟺ exact stationary terminal equilibrium on the cell; the replacement for `SwitchRepair`; formalization unblocked, not yet dispatched. |
| K4 regression exact resolution (`χ = (2/3, 0, 2/7)`, period-one orbit `(1, 2/7, 1)`) | `M [reported]` | Q166 Part A: the table was never residual — exact rational Nash–Bellman self-loop with quit mass 1, no sub-floor gaps, uniform packet defect 2/5; machine-check targets recorded in the seal. |
| `ℜ₃^local` residue (packet residues ∩ no two-owner root) | `I` | Exactly characterized, finite semialgebraic membership after adjoining exact χ; whether longer cycles/circulation absorb it is the next `n = 3` question (successor c2). |

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
