# Uniform-equilibrium mathematical frontier

The production theorem surface includes target-anchored payoff
closure, support-witness compilation, finite phase-occupation duality,
multi-owner face-circulation production, uniform-payoff reverse diagnostics,
boundary-holonomy tangent coordinates, the adaptive essential-APS compiler,
matching analytic projective packets, exact signed monodromy, finite charged
closing, punishment-completed cycles, and the truncated-ledger boundary
theorem. The adaptive compiler
removes a common hazard ceiling and geometric survival rate while retaining
pointwise proper hazards and the stated component hypotheses. Production Lean
is machine truth; checked experiments and uncommitted files are labelled
separately and do not become landed by appearing here.

## Conjecture and semantic waist

For every finite stochastic game, initial state, and accuracy `ε>0`, the
uniform-equilibrium conjecture asks for a behavioral profile and fixed target
payoff `v` such that one profile both delivers `v` and caps every unilateral
behavioral deviation for every sufficiently long finite horizon. The profile
may depend on `ε`; the target is fixed. Public finite memory, private memory,
clock dependence, and unrestricted behavior are distinct strategy classes.

Production `Uniform.lean` states the semantic predicate and its equivalent
quantitative deviation-cap constructor. The general existence theorem is one
of the repository's two intentional open declarations; the other is its
finite-quitting specialization. Verification of a supplied
certificate, synthesis in a bounded class, and coverage of all semantic
equilibria are separate claims.

The established consequence layer is diagnostic rather than productive:
profile-uniform vanishing payoff gaps preserve exact targets, bounded expected
potentials give the telescoping instance, tail width and excess work give exact
reverse characterizations, and rare transitions falsify unrestricted
transition-kernel continuity.  In finite quitting games, failure of every
uniform-equilibrium payoff is equivalent to one fixed positive terminal
exploitability gap against every behavioral profile.  This is an exact
counterexample target, not a finite certificate language by itself.

The counterexample restrictions now have one combined production interface.
Nonexistence is equivalent to a positive terminal gap `η` together with
finiteness of the canonical extended-real charge capacity of all exact
punishment-floor prefixes.  Dynamic debt is derived rather than independently
assumed:

`0 < η ≤ inf_N D_N ≤ D_N ≤ max_i max(0,r_i({i})) ≤ M`.

The optimized projective tail retains debt at least `η` for one owner and a
summable opponent clock.  The optimized tail itself has summable joint
absorption unconditionally.  More strongly, every unaugmented tail value
dominates the punishment floor: zero debt removes the augmented-cap term,
while positive debt is covered by the persistence theorem.  Hence every finite
chronological tail segment reverses to a legal exact floor prefix with exactly
the same absorption charge.  Every infinite
exact punishment-floor orbit also has summable joint absorption and converges
coordinatewise to all-Continue.  The canonical capacity defines a bounded
potential on the global boxed floor-admissible relation, so every recurrent
edge there has zero charge.  Segmentwise reversal does not make the
chronological tail one outward orbit from a fixed anchor, nor does it realize
its Bellman values as terminal payoffs.

The regime is empty below four players.  Any hypothetical finite counterexample
can be reindexed to a canonical cardinal-minimal `Fin n` table with `n ≥ 4`;
all nonempty proper restrictions are solved as restricted games, without an
automatic extension across excluded-player joining deviations.  Exact toggle
and stationary-cap ceilings, packet-support dynamics, and the division-free
floor budget
`(χ_i-v_s(i)) * opponentClock_i[s,∞) ≤ χ_i+M` give finite search filters.
On the charge side, every stable nonempty pure quitting coalition is a
unit-charge exact floor self-loop and therefore makes canonical prefix capacity
infinite.  This recovers the qualitative sure-exit exclusion independently of
the quantitatively stronger terminal-gap toggle theorem.

The forced packet also has a canonical scalar energy.  Its mass-weighted
delivery surplus is the quadratic form of the singleton solo-effect matrix;
the skew part contributes zero and the same energy is read by aggregate
refusal gains.  Every counterexample packet therefore supports two distinct
owners with positive reciprocal solo effect.  Conversely, if every reciprocal
pair sum is nonpositive, the packet is complementary and the existing
singleton-circulation compiler gives a uniform payoff.

Payoff terminology is fixed in
[`UniformEquilibrium/README.md`](../../UniformEquilibrium/README.md):
limiting-average, undiscounted-limit, and uniform finite-horizon notions are
not interchangeable without a named upgrade theorem.

## Established dependency chain for finite quitting games

The finite-quitting front is now sharply reduced.

1. **Terminal waist (`M+L+C`).** Terminal approximate Nash profiles for every
   accuracy exist iff a uniform-equilibrium payoff exists. See
   [the exact claim](../../ideas/QuittingGameConjecture/TerminalApproximateExistenceIffUniformPayoff.md),
   `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`, and
   `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
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

   The remaining boundary is now quantitatively rigid. Dynamic debt satisfies
   an exact survival-weighted conservation law, the selected owner's opponent
   clock has a logarithmic ceiling, actual late-tail payoff tends to zero, and
   the prescribed owner value stays at least `η`: the obstruction is a positive
   phantom continuation plateau, not hidden terminal delivery. A suffix's
   literal behavioral best-response value is within `2 M` times its remaining
   absorption charge of the best positive solo reward once that charge is
   below one; every summable tail has such sufficiently late suffixes. More generally,
   summable Bellman paths have a simultaneous annotation boundary with the
   same charge modulus, and every cofinally active player is pinned there to
   its singleton reward. Product independence also makes conditional
   multi-quitter mass at most `choose(|I|,2)` times the maximum stage
   absorption, with a matching singleton-mixture payoff approximation. A
   canonical source-typed window occupation retains all denominator cases and
   turns positive limiting owner mass into a literal active phase, hence into
   boundary pinning. These
   facts constrain a tail-derived occupation but
   do not supply funding or the punishment floor. On a supplied finite
   exact-debt return window, positive returning debt forces all opponents
   silent; two distinct returning coordinates force an all-Continue word.
   Every optimized
   debt cap belongs to the boxed punishment-floor carrier, while the underlying
   tail transitions remain separate from that carrier's charged relation. A
   displayed transition lifts exactly to an augmented-cap Nash--Bellman edge
   iff its diagonal seam vanishes; this is a local criterion, not a return or
   suffix producer. The
   original-coordinate outsider-`Never` calculation is now exact and extends
   through pure-time extremality to all behavioral deviations: its error is
   `eta + 2 M delta`. It remains conditional on a solo-continuation bound and
   small deleted insider absorption, neither of which follows merely by
   solving the restricted face. The
   refusal-conditioned occupation is compared to the original chronology by
   an explicit triangular-factor estimate. After normalization the error is
   divided by a positive joint-weighted deleted-absorption denominator; the
   canonical windows are not yet known to make this ratio vanish. The
   canonical compatible periodic windows are all terminally blocked and admit
   fixed-player/fixed-branch subsequences. This closes the compatible
   ultimately-periodic evaluator; it does not attach those suffixes to an
   arbitrary exact-D prefix or establish the general cap-splice realization
   premise.  More sharply, periodic attachment is governed by a normalized
   seam.  For an absorbing exact Nash--Bellman word with joint survival `C`,
   player-deleted survival `rho_i`, and endpoint drift `Delta_i`, the complete
   behavioral gain is bounded by the maximum of

   ```text
   C * [-Delta_i]_+ / (1-C)
   (rho_i-C) * [Delta_i]_+ / ((1-rho_i)(1-C)).
   ```

   These are exact branchwise formulas before the nonnegative finite-window
   slacks are discarded.  Thus `Delta_i -> 0` and compact recurrence do not
   suffice: the drift must vanish relative to the survival gaps.  In the
   refusal branch the positive dynamic debt is exactly capable of financing
   the surviving normalized term.  Even a valid identification of late owner
   occupation with the singleton packet would therefore identify two views of
   the same refusal defect, not produce a contradiction.  The
   `rho_i = 1` isolated coordinate is the separately classified negative-solo
   exception.  The optimized counterexample tail is now known to lie on the
   opposite side of the joint normalization: there are `speed > 0` and a late
   date such that every positive-absorption window satisfies
   `dist(v_n,v_m) >= speed * (1-S_nm)`.  The proof uses collision concentration,
   compact normalized singleton occupation, all-date punishment rationality,
   and the uniform packet defect.  Thus no selected-tail window returns at
   little-o of absorbed-mass scale.  This ballisticity is not recurrence;
   summable absorption permits a bounded path to approach its limit at nonzero
   clock speed.  The signed normalization is now retained as a
   `QuittingChargeTangentPacket`: unless the tail is eventually literally
   all-Continue, a subsequence of positive one-stage windows has convergent
   owner occupation and normalized endpoint tangent, with tangent equal to
   singleton delivery minus the phantom boundary.  Every counterexample
   tangent is either negative in some coordinate or positive on an active
   owner after negative coordinates are excluded.  Converting those signs
   respectively into phase repair or support enlargement is the immediate
   frontier.
6. **Two endpoint charts (`M+L`).** Reading the same minimizers from both ends
   gives a forward positive-debt ray and a reverse ray ending on the terminal
   face with a quantitative depth-one packet. The middle length still diverges.
7. **Finite middle algebra (`M+L`, `e1fe7dc`).** Every actual finite middle has
   an associative multiplayer `QuittingBoundaryHolonomy` with exact prescribed
   `(B,P)` and arbitrary-behavior `(A,T,χ)` semantics, source roots, exact-D
   endpoints, and packet provenance. Fixed-word cap safety is affine. The
   `6cd0a24e` tangent layer adds exact residual cocycles, self-similarity,
   max-plus tangent dynamics, and compact subsequences of realized coordinates,
   but not a closed realized image or strategic decoder.
8. **Fixed-cutoff topology and the length fence (`M+L`, `14d75ff`).** For each
   cutoff, the resolved graph retaining the complete source path and all legal
   subblock holonomies is compact and closed. The fixed-last calibrated lift
   is finite and retains the selected minimizer, owner, marked action,
   exact-D endpoints, survival, atom, and common holonomy. Conversely, every
   compact subset of `ℕ × X` has bounded length, so no compact lift retaining
   literal unbounded game-stage cost can cover the escaping middles.
9. **Infinity chart: generalized completed traces (`M`, partial).** Published
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

   The compact numerical core has now been audited.  Anchored straight-chord
   vector-factor chains form a compact Hausdorff hyperspace and continuously
   determine full/deleted survival and, with the terminal vector fixed or
   stored, the prescribed origin value.  A compact marked obstacle set
   determines its cap continuously.  Finite density in the jointly defined
   closure is definitional.

   The proposed bare carrier is not decoder-complete.  A hypograph over mass
   retains only the fibrewise obstacle envelope, not repeated-mass chronology;
   ambient splice continuity and closed anchor equality do not give exactly
   composable finite approximants or self-seam pullback.  The defensible target
   is the joint semantic-graph closure of trace, coalition path, marked obstacle
   graph, holonomy, anchors, debt, packet, and compact provenance. See
   [`CompletedVectorFactorTraceIsCompactAndDetermining.md`](../../ideas/PositivePlateauBoundaryClosure/CompletedVectorFactorTraceIsCompactAndDetermining.md)
   and `PC-012` for the audited scope and open gates.  Exact seam pullback is a
   separate obligation for complementary-cylinder surgery; the behavioral-tail
   decoder of `PC-013` instead recomputes actual gain across the physical seam.
   The claimed
   aggregated-carrier fallback failure (fibres carrying different origin
   values at the same obstacle trace) is likewise `M [reported]`; see
   [`AggregatedCarrierConflatesOriginValues.md`](../../ideas/PositivePlateauBoundaryClosure/AggregatedCarrierConflatesOriginValues.md).
   The exact finite adapter remains unproved regardless.

The chain is exhaustive up to the positive fully summable plateau. It is not a
claim that every equilibrium belongs to one finite grammar.

## LCP normalization and the strict abnormal base case

The quitting LCP layer retains the literature's playerwise solo normalization
without pretending that the translated game still has zero payoff on
nontermination. Its explicit payoff table assigns the negative solo baseline
to Never and proves, for every behavioral profile, that normalized terminal
payoff is original terminal payoff minus that baseline. Terminal
approximate-Nash inequalities therefore transport in both directions at the
same error.

The normalized singleton matrix is the existing projective comparison matrix.
For an arbitrary matrix, the simplex/projective `Q` convention is exactly the
disjunction of textbook standard `Q` and a homogeneous simplex solution.
Projective `Q-bar` is imposed separately on every nonempty principal
submatrix. These are algebraic facts; no stationary, public-correlation, or
continuous-path conclusion is bundled into their definitions.

The literal published recursive normal-player formula collapses after
zero-diagonal normalization because a player can witness itself. Production
Lean proves that collapse and defines the distinct-witness recursion separately
without attributing unproved source consequences to it. The resulting
five-way theorem is an exhaustive matrix-regime gate, not a strategic
classification.

One strict strategic base case is closed. If the first corrected normal layer
is empty, every player strictly prefers every other player's solo absorption
to its own. Either all solo rewards are nonpositive and Never is exact, or a
positive-solo owner admits a positive stationary hazard satisfying every
inactive joining inequality. In both cases one exact stationary terminal Nash
profile exists, and its terminal payoff is a uniform-equilibrium payoff.

The later-layer all-abnormal construction, homogeneous and non-`Q` stationary
producers, concrete sunspot semantics, projective-`Q-bar` continuous paths, and
the absorption-path-to-ordinary compiler remain open.

## Essential APS on the singleton-flow stratum

The essential-APS layer formalizes a genuine but conditional positive stratum.
Inside compact convex carriers with a functional unique-live Flesch successor,
the greatest fibers are convex and compact. Terminal-free fibers admit one
coherent infinite executable run, rather than unrelated finite paths. Uniform
finite-window face avoidance forces positive mass in every shifted window;
strict Flesch cross-gains and bounded drift force every opponent mass to
diverge; product/sum accounting gives qualitative deleted-player survival
decay. Finite adaptive subdivision at each coarse stage with `p_t < 1` preserves
survival and exact Continue transport while making the immediate-Quit error
uniformly small. The nonperiodic Snell supersolution therefore
proves that every initial point in the component is a uniform-equilibrium
payoff.

This does not close the quitting-game problem. The structural hypotheses are
not derived for arbitrary games, so no arbitrary game is asserted to contain a
nonempty component of this kind. But the former local root-Nash gap inside the
component is closed. The mesh compiler is stated more generally for any
bounded viable singleton-flow path with qualitative deleted-player survival
decay; fixed ceilings and block contractions are stronger specializations. A
supplied finite proper cycle remains a separate positive
stratum. The durable interface and exact theorem map are recorded in
[EssentialAPS.md](EssentialAPS.md).

## Support-witness quitting paths

Retaining the support-local one-stage witness gives a deterministic alternative
to the abstract rank-one crossing route. Each ledger increment is bounded by
`delta` times the player's own Quit probability, so the product--sum survival
inequality forces every ledger crossing to occur no earlier than an own-survival
crossing. The first such crossing supplies joint reach for the marked player
and deleted reach for all other players. Player-specific closed tails obtained
from approximate individual rationality then compile a completely absorbing
path to terminal Nash error

```text
2 delta + r + sqrt(delta) (2 + 7 M).
```

Divergent total absorption is sufficient, and a finite witness-retaining cycle
with one positive-absorption phase compiles to such a path. These are genuine
consumer theorems and they close the relaxed per-tolerance compiler
(`MATH-P0-8`), but not the producer for arbitrary games: support optimality,
all-time individual rationality, and divergent absorption (or the corresponding
finite cycle) remain hypotheses. See
[SupportWitnessCompiler.md](SupportWitnessCompiler.md).

## Projective analytic packets, signed monodromy, and finite charged closing

On the matching vanishing-discount branch, where the quit-family analytic
order equals the germ ramification, the first-event denominator has leading
coefficient `1 + L`.  `UniformEquilibrium/Quitting/Projective/AnalyticFirstEvent.lean` therefore
extracts canonical cemetery mass `1 / (1 + L)`, singleton masses
`a_i / (1 + L)`, and vanishing normalized nonsingleton mass without passing to
a subsequence.  The game-facing analytic packet theorem uses the exact Bellman
identity and endpoint complementarity on the physical slice
`0 < t < min(g.radius, 1)` to
identify the endpoint value with the singleton reward mixture and obtain the
normalized singleton LCP packet.

Packet extraction does not certify its endpoint as an undiscounted strategic
target.  `UniformEquilibrium/Quitting/Projective/TargetMismatch.lean` gives the sharp regression:
a genuine order-one analytic equilibrium branch has cemetery and two
singleton weights all equal to `1/3` and endpoint `(1,1)`, yet terminal
`epsilon`-Nash and coordinatewise `delta`-closeness imply
`1 - delta <= 4 (delta + epsilon)`.  In particular equal errors are at least
`1/9`, so `(1,1)` is not a uniform-equilibrium payoff.  The same game has exact
uniform payoffs `(1,2)` and `(2,1)`.  The cemetery coordinate therefore needs
an executable continuation contract; an affine anchor alone does not make the
packet target credible.

This closes analytic packet extraction in the matching regime and fixes the
next interface: accept the packet target with strategic continuation data, or
reject it and retarget through a proved alternative.  On an accepted target,
resolved-chart construction, physical arc lifting, semantic Farkas decoding,
and production of sufficient real absorption remain independent obligations.

At the consumer end, `UniformEquilibrium/Quitting/Projective/SignedProjectiveLasso.lean` records the exact
invariant: survival-weighted signed Bellman monodromy equals aggregate
absorption times the difference from the actual periodic value.  Thus the
rotation-uniform signed bound is equivalent to periodic-value closeness.
Absolute-weighted variation remains a stronger compatibility interface; a
formal two-phase example separates the two acceptance tests for one fixed
candidate, although their all-accuracy existential producer hypotheses are
equivalent through exact-cycle correction.

`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean` gives a second, sharper upstream
adapter.  For every tolerance, compactness first selects one finite charge
threshold.  Any exact forward packet reaching it contains a close returned
block with raw charge at least one; reversing the block leaves one closing
seam, and its aggregate absorption is at least one half.  Hence the producer
may have quantifiers `for every charge target, some finite packet`: one orbit
working for every target and a separate rotation-recurrence theorem are not
required.  Repetition of a label without large total charge still gives no
such conclusion.

## Punishment-completed exact cycles

There is also a reward-perturbative route to exact cycles.  The production
strata distinguish raw cyclic Nash--Bellman consistency from an absorbing,
punishment-admissible solved cycle.  Solved cycles compile to uniform payoffs,
and if their reward tables accumulate at a given table then fixed-skeleton
reward closure supplies a uniform payoff at the limit.  Contrapositively, any
hypothetical counterexample is separated by a positive reward-table radius
from every solved exact cycle of every finite period.

For a supplied fixed root cycle,
`UniformEquilibrium/Quitting/Cycles/OwnShiftCycleExactification.lean` gives the
exact global equations for perturbing all terminal coalitions containing a
player by one common player-specific amount.  Phase values cannot be corrected
independently: they satisfy a cyclic affine feedback recurrence.  When the
cycle absorbs, that recurrence has a unique solution, its unit multipliers lie
in `[0,1]`, and all correction variables eliminate player by player to a
finite system in the reward shifts alone.  This makes one perturbation stratum
decidable and search-facing.  It does not show that the reduced system is
feasible, that solved strata are dense, or that this low-dimensional shift
family captures general coalition-reward perturbations.

The exact-cycle compiler no longer needs every noncontracting coordinate to
have nonnegative solo payoff.  In
`UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean`, each coordinate may instead satisfy
either strict deleted-survival contraction around the cycle or the inequality
that its punishment value is at most its selected solo value.  An exact
absorbing Nash--Bellman cycle with this coordinatewise certificate yields its
selected phase value as a uniform-equilibrium payoff.  The older admissible
cycle theorem is recovered because nonnegative solo payoff dominates the
punishment floor.

For a sure solo exit, `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` gives the exact
characterization: the owner's solo payoff must dominate its punishment value,
and no outsider may gain by joining at the first stage.  This is a genuine
positive result for isolated negative solo values, but it does not prove that
every isolated-negative branch supplies the required punishment inequality or
that every weight produces an exact cycle.

## Truncated-ledger certificate boundary

The all-errors truncated-ledger package remains a sound sufficient route to a
uniform payoff.  It is not a universal producer target.  The formal two-player
zero-sum table in `UniformEquilibrium/Quitting/Debt/Ledger/TruncatedLedgerCapCounterexample.lean` has the exact
all-Continue uniform payoff zero, yet no package at tolerance `1/2`: deviation
accounting forces the common reach parameter above `1/2`, while the package
error budget forces it below `1/10`.  Thus any complete argument must retain a
persistent-live branch or weaken the common all-player deleted-survival
condition; the former reduced-cap conjectural leaf is removed.

## Multi-owner face-circulation producer stratum

A supplied bounded `FaceCirculationCertificate` is now a genuine conditional
producer class. If phase support sizes are bounded, every phase ratio is at
most one common `a < 1`, and its floor dominates formal
`quittingPunishmentValue`, balanced owner words yield a forward orbit with
Bellman transport, support-local approximate Nash rows, and a uniform positive
absorption lower bound.  The finite-quantifier theorem now closes directly:
arbitrarily charged finite forward packets in a common compact carrier contain
a returned one-seam block and therefore produce a uniform-equilibrium payoff.
The earlier infinite compact-reversal path remains a compatible route, but is
not needed to strengthen `for every charge target, some packet` into one orbit
uniform in that target.

The compact reversal does not formally identify that payoff with a named
circulation vertex. The theorem also does not construct a certificate for an
arbitrary game, so the arbitrary-game producer remains open. The scaled cyclic
weight and the repaired four-player stress weight `(x, lambda) = (2, 1)` are
concrete corollaries. The exact interface is recorded in
[CirculationUniformPayoff.md](CirculationUniformPayoff.md).

Finite phase-occupation LP/duality is an adjacent verification stratum: given
a phase occupation, it proves semantic strong duality, an optimal occupation,
and a phase-bias dual certificate. It does not prove occupation nonemptiness
and is not a strategic producer.  A future occupation synthesis must be
componentwise: global cancellation across recurrent SCCs need not be realized
by any legal path, and even a circulation inside one SCC needs a connector and
signed-discrepancy theorem. Equal-atom material remains unformalized and is
only a possible future intake target.

## Fixed-skeleton payoff closure

Uniform stage-reward perturbations leave all finite-history laws unchanged and
move every baseline or deviating finite-horizon payoff by at most the reward
distance. Consequently an `epsilon`-Nash profile in the nearby game is an
`epsilon + 2 rho`-Nash profile in the original game, with the same horizon
threshold. Selected-target sequential closure is proved without taking a limit
of strategies. The target-free existence-set closure uses only compactness of a
bounded finite-dimensional payoff cube; this turns dense coverage by solved
payoff tables into full fixed-skeleton coverage. Transition-kernel perturbations
are outside this result. See
[PayoffPerturbationClosure.md](PayoffPerturbationClosure.md).

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
certificate after compact closure.  The finite representation layer is now
exact: every realized block maps to a source-forgetting joint stage graph, its
chronological composition is associative, the encoder commutes with adjacent
block concatenation on every coordinate, and strong semantic coherence is
closed under exact-anchor splicing.  Affine prefix and suffix marks make these
laws division-free even at zero survival.

Boundary objects representing an escaped infinite or continuous middle are
still unavoidable unless plateau middles are uniformly tight.  The leading
candidate for that compact completion is the
[marked absorption-path route](../../ideas/PositivePlateauBoundaryClosure/EnrichedAbsorptionPathsMayCompactifyTheEscapingMiddle.md), with the
[escaping-middle problem](../../ideas/PositivePlateauBoundaryClosure/RealizedAnchoredHolonomyClosedness.md)
retained as its acceptance/falsification test.  The next theorem must construct
the generalized closure and expose continuous holonomy, packet, and debt
projections.  Compact provenance for identical zero-mass stages, completed
`Never` semantics, generalized mark transport, and exact-seam/self-seam finite
pullback remain additional obligations; compactness and density alone do not
supply them, but physical behavioral-tail attachment does not require the seam
pullback.

The strategic decoder's all-length tail layer has a quitting-specific positive
resolution at the behavioral seam (`M`, formalization active).  A fixed prefix
acts on every tail through affine/max-affine holonomy with one Lipschitz modulus
independent of tail length.  Every behavioral tail is semantically approximable
by a finite word followed by sure joint exit, sure solo exit, or Never, using
the trichotomy of full and deleted survival limits.  Hence the all-tail repair
value is Lipschitz: it yields either one finite elementary tail stable near the
prefix holonomy or a neighborhood-stable floor against every tail.  The open
gate is now prefix consumption.  A positive floor after one calibrated prefix
does not itself exclude a profile that replaces that prefix.  The required
variational theorem must either construct a controlled exact-`D` competitor
whose calibrated objective drops in proportion to the floor times retained
packet mass, or lift the obstruction to a literal global terminal
exploitability gap.  A plateau-null separator is useful only with the dual
occupation-balance theorem forcing its nonnegative integral to vanish.
Compactness is needed only to uniformize the resulting local prefix charts.

Local Bellman complementarity cannot replace this theorem.  A one-player
negative-quit game has an exact Never equilibrium, yet a sure-quit prefix can
be complementary relative to a stored negative endpoint and still have a unit
physical all-tail floor.  The selected minimizer and calibrated replacement
structure, not the local prefix semantics, must provide the consuming force.

The optimizer interface also matters.  The original marked terminal anchor is
selected from the min--max debt optimizer, whereas the strongest landed
prepend calibration controls the aggregate optimizer.  A decrease in one
marked coordinate need not reduce a tied maximum.  A distinct
aggregate-calibrated marked anchor now retains the canonical aggregate path;
the direct route uses it unless a new min--max theorem controls all active
maximizers.  Optimizer provenance may not be erased at this seam.

The normalization across that seam is now exact.  For the complete canonical
aggregate prefix, Never evaluates to the exact dynamic-debt vector, so its
all-tail repair value `E(H_n)` is at most the aggregate optimum `d_n`.
Quantitative owner and terminal-atom selection then gives
`d_n ≤ 2 M |I| |I → Bool| packetMass`.  Thus a positive floor cannot lose its
marked scale.  What remains is a mark-aware Nash-compatible retargeting theorem
which reselects the entire exact prefix with controlled aggregate decrease, or
turns failure into a genuinely global terminal deviation certificate.

Production formalization is partial and follows this mathematical split.  The
fixed-prefix holonomy module proves the common playerwise/aggregate gain
modulus and its fixed-family infimum consequence.  The behavioral
specialization defines the actual all-tail infimum from same-tail prescribed
and literal best-response coordinates and proves its Lipschitz and buffered
repair/floor consequences.  Exact infinite phase-switch evaluation identifies
each such holonomy gain with literal terminal exploitability of the attached
profile and therefore identifies the two infima; it needs bounded rewards but
no absorption or survival hypothesis.  The tail-compression module
provides the elementary caps, full/deleted-survival trichotomy, exact Never
boundary pair, positive-survival prescribed convergence, and the complete
all-deleted-zero sure-joint branch in both prescribed and literal behavioral
best-response coordinates.  The sure-solo owner has exactly the Never
deviation envelope.  The sharp Never coupling bounds every pure quit time, and
then the literal behavioral supremum, by
`2 M (χ_i(N) - χ_i(∞))`.  The combined three-case capstone now selects one
finite cap and cutoff which simultaneously approximate all prescribed and
best-response coordinates.  The fixed-prefix boundary-pair modulus transports
that approximation to maximum positive gain, and elementary capped tails have
exactly the same repair-value infimum as all behavioral tails.  This completes
the fixed-prefix tail decoder; code length may still diverge with accuracy.

The prefix-consumption inputs now preserve the relevant optimizer provenance.
An aggregate-calibrated marked anchor retains the canonical aggregate
minimizer and its positive separated packet, matching the landed prepend-loss
theorem.  The negative one-player prefix fence is also machine-checked: a
sure-quit row is locally complementary at stored endpoint `-1` and physically
has unit gain against Never, although Never is an exact terminal equilibrium
of the game.

**The bounded root-debt descent decoder is closed negatively (`M`)** — see the
capstone claim.  No bounded-length exact-`D` modification achieves a cutoff-
independent decrement, and accumulation does not rescue it.  This does not rule
out attached repairs outside the source grammar.

**But the plateau driving that closure is manufactured by the zero pin (`M`).**
Both known plateau witnesses are two-player tables that have exact equilibria
with debt zero once the terminal continuation is unpinned, and both equilibria
are machine-checked: player one mixes at rate `1/2`, player two never quits,
values `(a,0)` and `(1/4,0)` respectively, with both coordinates exactly
indifferent and absorption rate `1/2`. The pin forces a strictly positive gap
at every finite horizon, which forces the opponent survival product below one,
which creates the debt; let the gap go to zero and the plateau vanishes.

So zero-boundary exact-`D` is a calibrated **source** grammar, not a restriction
on the repair output. A positive plateau in that grammar is evidence it may
have missed the equilibrium.  A free terminal continuation is valid only when
one admissible tail co-realizes both the prescribed boundary value and the
best-response boundary envelope; matching two scalars by fiat is not a
strategy. `PC-009` and `PC-012` retain the enriched absorption-path route with
this corrected decoder scope.

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

`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`
defines `QuittingInstantPunishmentWorks`, allows an arbitrary continuation
after a refused stage-zero quit, proves its exact equivalence to punishment
individual rationality plus the no-join inequalities, and compiles either pair
of conditions to a uniform-equilibrium payoff. The missing condition is a
**producer**, not expressibility: the global branch analysis does not
force some owner to satisfy both instant conditions, nor does the instant
theorem consume the strict-slack or enlarged-support residues by itself. The
deficient deleted-clock case is consumed separately by owner-monopoly
concentration and approximate solo punishment completion.

**The punishment target is explicit (`L`).** `PunishmentLevel.lean` supplies a
finite-horizon min-max level,
individual rationality in exact and approximate form, and the necessary
condition that a uniform equilibrium payoff is eventually approximately
individually rational. The `χ` in the older quitting files is an unrelated
best-response-summary coefficient — a name collision, not a punishment notion.

The folk bill contains two proved components.
`UniformEquilibrium/Quitting/Punishment/Floor.lean` gives the unconditional
floor `max{(T−1)/T·mIn, mOut}`, the
sandwich converging to `max 0 (solo)` under two finitely-checkable table
conditions, and exactness on the hostile witness. Its no-go generator proves
that zero is not a uniform-equilibrium payoff of the quit-bonus table, with
margin `1/4` from horizon `4`. `Feasible.lean` supplies the finite-horizon and
asymptotic feasible sets,
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

**The low-dimensional capstones are complete**: every two-player quitting
game has a uniform equilibrium payoff by
`quittingGame_exists_uniformEquilibriumPayoff_twoPlayer`, using a direct
four-branch classification. Every three-player quitting game has one by
`quittingGame_exists_uniformEquilibriumPayoff_threePlayer`. The latter
starts from an unconditional analytic Bellman germ, translates absorbing
auxiliary endpoints through punishment-admissible closing, and classifies an
all-Continue endpoint into Never or a normalized singleton source. A finite
three-coordinate alternative then yields either a complementary face
circulation or one of the two strict directed singleton cycles. The
three-coordinate alternative is dimension-specific; the unresolved quitting
frontier begins at four players.

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
- `UniformEquilibrium/Quitting/Cycles/PeriodicFiniteHorizonRate.lean` proves a conditional mesh compiler:
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
  three-player absorbing games are settled (Solan 1999); the repository now
  contains unconditional quitting-game capstones for both two and three
  players;
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
| Uniform-payoff closure and reverse diagnostics | `M+L` | Fixed-skeleton reward closure, target equivalence under vanishing payoff gaps, tail-width and bounded-work characterizations, and transition-discontinuity counterexample landed; no forward producer. |
| Support-retaining path/cycle compiler | `M+L+C` conditional | Landed; path or finite periodic witness production at every tolerance remains open. |
| Essential-APS adaptive compiler | `M+L+A+C` on the stated component | Landed for compact functional unique-live terminal-free components with finite-window face avoidance; exact segment closure on any owner carrier also gives finite terminal execution or an infinite exact APS run. Algebraic invariance and balanced occupation alone do not supply chronology. Arbitrary-game component production and the full-jump boundary remain open. |
| Multi-owner face-circulation producer | `M+L+A+C` conditional | A supplied bounded circulation above punishment value produces arbitrarily charged finite packets and a uniform payoff by finite charged closing; generic certificate existence remains open. |
| Signed projective monodromy | `M+L+C` conditional | Exact cyclic correction coordinate; strictly weaker than absolute seam variation for a fixed candidate, but not a weaker all-accuracy producer hypothesis. |
| Finite charged closing | `M+L+A+C` conditional | Arbitrarily charged exact finite forward packets in one compact carrier yield a returned single-seam lasso and uniform payoff; no orbit uniform in the charge target is required. |
| Punishment-floor finite-prefix producer | `M+L+A+C` | Every finite quitting game has exact product-root predecessor prefixes above the behavioral punishment floor. Either target-dependent prefixes have arbitrarily large charge and finite charged closing yields a uniform payoff, or one common finite bound controls every exact prefix in the canonical box with a punishment-rational anchor. On the global boxed floor-admissible exact-predecessor relation this is an exact finite budget with a canonical least bounded potential decreasing by the literal absorption charge. No single-orbit selection theorem is needed; strategic realization of the bounded branch remains open. |
| Finite phase-occupation duality | `M+L` conditional | Semantic/LP equivalence, attainment, bias decoding, and strong duality landed conditional on feasible occupation; strategic occupation production is not included, and global cross-SCC cancellation is not path-realizable. |
| Quit-time/Never extremality for behavioral deviations | `M+L` | Landed. |
| Exact-D optimizer and zero/positive split | `M+L+A+C` on zero branch | Landed. |
| Combined counterexample normal form and finite screens | `M+L+A+C` | Nonexistence is exactly positive all-behavior terminal gap plus finite canonical floor-prefix capacity. The regime is empty below four players and has canonical minimal `Fin n` form; toggle/stationary ceilings, supported packet atoms, closed weak-preference walks, quantitative floor-clock budgets, and zero-charge recurrence are landed. Proper restriction and packet-support cycles are explicitly not ambient extensions or chronological Bellman orbits. |
| Periodic-window and phantom-boundary evaluation | `M+L` | The full behavioral reply against periodic opponents is exactly a finite phase-stop/refusal maximum. Conditioning on eventual absorption removes the phantom boundary while retaining exact consecutive chronology. Singleton rows purify exactly. On the diffuse singleton-tight stratum, hazard rescaling has quadratic coalition-law error. Complete deleted clocks feed a two-clock compiler. A deficient clock forces a unique nonsummable owner, summable non-owner hazards, and literal terminal convergence to the owner's singleton vector; direct conditioned solo extraction and punishment completion compile the owner whenever the rescaled pure-Quit defect vanishes. Exact source Nash charges every singleton-floor deficit to the source deleted clock, so no source-floor premise is required. Hence a diffuse positive-absorption counterexample seam has a strict phantom coordinate `solo_i < boundary_i`; every such player is eventually literal `Never`, and the quitter support lies on a proper singleton-tight face beyond a common cutoff. One fixed outsider recurs cofinally with a uniform rescaled Quit defect, a conditioned payoff uniformly below its singleton reward, and a uniform positive endpoint gap against the next conditioned target. Unmodified targets split into floor-admissible reset targets or a fixed underfloor coordinate funded by phantom survival. Coordinatewise floor clipping gives a sharper scalar alternative: a distinct negative singleton or exact punishment/singleton equality, or cofinally many exact Nash--Bellman reset edges with both endpoints above every punishment floor and uniformly positive absorption. These displayed edges cannot compose because every tail stores the all-Continue simplex. Own-marginal approximate repair causes an order-one predecessor displacement, while full-root tail stability consumes any supplied full-vector match. Approximate root/continuation splicing needs no sure-absorption premise. The residual is multi-player chronological matching with a nontrivial stored tail root, or exclusion of the scalar punishment/singleton branch. |
| Conditioned periodic renewal | `M+L` | Longer finite windows of the canonical source tail can be repeated as ordinary periodic product profiles. Their literal payoffs are exactly the normalized restart deliveries and converge to the source value conditioned on eventual absorption. Their full caps are the exact refusal/first-pass phase-stop maxima. This closes payoff provenance but not renewal tightness: maximum- or total-debt minimality supplies no upper bound on the cyclic cap, whose stabilized exercise or passive-refusal excess is the exact residual. |
| Cap--Nash endpoint transport and chronology | `M+L` | Prefix an actual profile by an exact mixed Nash root selected against its coordinatewise behavioral cap. Every literal best-response debt and the uniform random-deviation audit loss scale exactly by joint Continue mass, so positive total-debt infimum charges absorption and survival odds to relative excess above the infimum. A sharp joining-loss constant transports singleton endpoints to the cap. Against `cap-q`, one auxiliary root simultaneously gives a near-minimum absorption moat and a prescribed/comparison singleton floor; this excludes a persistent conditioned endpoint gap on any co-realized total-debt near-minimizing family. Under an explicit strict comparison of the moat errors, every exact Nash root against the unshifted cap is literally all-Continue. Arbitrary-depth finite backward cap chronologies still exist, but `D_*` times their unweighted total absorption is at most the terminal debt excess, each finite block's survival stays uniformly positive, and payoff/cap return is only linear in absorption. A distant debt target forces macroscopic absorption, yet the exact conditional-delivery split leaves cancellation or root selection as the renewal obstruction. The cap-to-prescribed homotopy is all-Continue before its endpoint at a positive minimum; its endpoint is either still all-Continue or a solo debt gate with a joiner/punishment certificate, and an honest regression stalls on the whole closed homotopy. Stacks at different depths need not be compatible, so no infinite Never path, tangent, or renewal-tightness conclusion follows. |
| Collision-aware and singleton return compilers | `M+L+A` conditional | Any supplied finite collision-aware exact Nash return with punishment admissibility is a solved exact cycle. On proper singleton roots, a changing-owner state-matched Nash--Bellman cycle is already an essential-APS cycle and compiles without an extra punishment field. Counterexample data currently supplies neither a finite return nor a divergent singleton chronology. |
| Eventual all-Continue plateau | `M+L` | The branch is eventually an exactly constant positive-debt phantom state and literally delivers zero. Its selected owner has singleton reward at least the terminal gap, every positive solo rate has a strict joining blocker, and any exact singleton-target Nash root must enlarge support to a second quitter. The residual is the enlarged root's simultaneous complementarity/rate selection, not late dynamics of the plateau. |
| Literal terminal-debt prefix action | `M+L` conditional | Here debt means the best-response debt, equivalently the all-behavior unilateral regret or exploitability gap, not online-learning regret. The global infimum of literal maximum terminal exploitability is positive in every putative counterexample. Exact Nash prefixing acts coordinatewise by `d ↦ (c*d-a)₊`; chronological blocks compose exactly and the summed debt loss is opponent-killed debt plus consumed positive endpoint premium. Arbitrarily deep finite exact-root stacks exist over lexicographic near-minimizers, with every displayed suffix pair literally co-realized and every local total drop below the common accuracy. A macroscopic debtor sees vanishing opponent hazards and premium; two macroscopic debtors force the whole root toward all-Continue. On one actual profile, affine deconditioning transports a same-player positive singleton and conditioned-endpoint gap to literal debt uniformly over every absorption regime. The projective conditioned tail does not co-realize those inputs automatically, and plateau-realizing profiles provably have the opposite conditioned-endpoint sign. The remaining live use is on a different marked actual family, not the plateau sequence itself. |
| Literal terminal semantic equality stratum | `M+L` | The compact prefix-invariant semantic carrier has positive minimum total and maximum best-response debt in every counterexample. Auxiliary selection forces every positive minimizer of either objective to be an all-Continue self-loop. One actual pure-time law pays debt through quantitative harmonic Never mass or chronological charge. In the persistent collision branch, atom mass times the marked quitter's local defect is bounded by reset debt, so the same executable rows have vanishing marked-player defect. Their tail cluster either lies strictly above the minimum fiber or, on the fiber, other players carry a uniform positive defect sum. A reached-row better-endpoint switch is a legal unilateral deviation with exact gain `live mass * local defect`. Its marked coalition is routed with no loss into exactly one of four same/erase/insert/same Boolean cells. Fractional switching reduces the same debt exactly and retains at least `1-lambda` of every incidence atom; its transfer account loses the actual prefixed source's exact excess over the minimum, because localization only puts the continuation tail on that fiber. If a finite reset word reaches zero total root defect from positive collision mass, some full member-Continue move carries positive mass from an exact pair to its singleton. The singleton either lies in the isolated-negative punishment branch or admits a distinct strict joiner whose pure-Quit update creates an overlapping positive-mass pair; this is a static root transition, not a Bellman edge. General exit-face Nashification is false even approximately, and iterated legal resets can destroy the collision and end at zero-absorption all-Continue. The counterexample has a finite closed strict-toggle orbit on the coalition cube, but not a Bellman chronology. Coupled reset/incidence flows cannot obtain provenance from the coordinate-conserving minimum spine. Cap--Nash prefixing of an off-minimum reset cluster instead has an exact excursion account. The compact joint semantic/full-outcome-law carrier permits fixed-law reset minimization, retains transfer and incidence, and transports incidence as `root incidence + survival * old incidence`. At that minimizer a singleton-cap violation yields strict absorbing descent with positive survival; otherwise all-Continue is a cap fixed point. Positive incidence and a supported strict toggle do not eliminate this face, by a literal exact regression. On the positive-incidence reset face, minimizing debt first gives an exact dichotomy: contact with the global minimum fiber, or positive separation. In the separated case the surface tension `(D-D_*)/I` attains, and its division-free maximum principle forces every exact cap--Nash root to all-Continue. For each fixed positive incidence threshold this unique cap root has a robust positive total-defect moat. A fixed normalized three-player table keeps incidence at least one half while total defect tends to zero, so no linear moat persists uniformly into the diffuse-incidence scale. The harmonic and finite reservoirs can be retained on one co-realized reset law and fed to the fixed-law dispatch. The live gap is a compiler from the separated all-Continue joint-law plateau to a finite reset word or state-matched chronology, or a strategic consumer of the isolated-negative/replacement pair transition. Boolean Möbius labels remain upper charges and can cancel to zero net defect. |
| Reset-face reprojection | `M+L` | At a separated surface-tension plateau, exact support on the reset face extends uniformly with arbitrary additive error to points of sufficiently small reset debt. The quantitative extension has an exact alternative: either one linear face penalty controls the whole joint carrier, or positive off-face violations have unbounded violation-to-reset-debt ratio. The unbounded branch concentrates at a joint semantic/law contact with zero reset debt and tension, strictly positive opponent incidence, and exact reward-moment provenance; along its approach, reset debt is negligible relative to tension. These independently co-realized carrier points furnish neither a common absorption-normalized Bellman window nor a chronological edge. |
| Harmonic reservoir obstruction | `M+L` | At a minimum debt gate with no strict singleton joiner, the harmonic/Never branch produces a fully absorbing sure-solo row which is locally exact. Its unique noncontracting owner has stationary unilateral cap zero and regret at least the selected debt share, while `solo < punishment ≤ 0` reverses the punishment-admissibility inequality. Thus neither a period-one completed cycle nor an arbitrary instant-punishment continuation consumes this branch. |
| Approximate punishment completion | `M+L` | Absorbing fixed-period cycles compile under vanishing root error normalized by deleted contraction. In the sole-owner case, arbitrarily small positive hazards and approximate endpoint Nash at continuations converging to the singleton vector suffice, provided the owner is punishment-rational. This removes the need for an atomic lower hazard bound. |
| Augmented-cap carrier, terminal funding, and splice | `M+L` | Finite exact-D caps lie in a bounded punishment-floor carrier. The aggregate terminal singleton cap is at most the reward bound and cannot saturate the older cardinality bound in a counterexample. The canonical one-owner zero-target funding root is always Farkas; any physical funding root must enlarge support and use negative collision payoff, and compatible two-owner zero-pair-join support is insufficient. Cap-minus-value transports exactly by survival, but common terminal realization and a strategic return remain open. |
| Owner clock/packet and two-ended core | `M+L+A` | Landed; stronger preselected-mark bridge products remain mathematical/experimental. |
| Finite-block boundary holonomy | `M+L` | Landed at `e1fe7dc`. |
| Fixed-cutoff resolved holonomy graph | `M+L` | Compact/closed with full source path; fixed-last calibrated lift finite, in `UniformEquilibrium/Quitting/Boundary/Holonomy/Compactness.lean` at `14d75ff`. |
| Boundary-holonomy tangent coordinates | `M+L` | Residual cocycles, self-similarity, max-plus tangent dynamics, realized bounds, and compact coordinate subsequences landed; realized-image closedness, source retention, producer, and decoder are not included. |
| Greedy return/exit/dead-end | `M+X` | Checked experiment, natural abstract stopping point; not production/decoder. |
| Metrizable marked-semantic completion and decoder | `M+L` | The compact metric quotient has sequential finite density, exact finite-cylinder specialization, continuous bounded holonomy and obstacle decoding, repair-value continuity, and finite subsequence realization of repair-state limits. It is semantic infrastructure, not a strategic orbit producer or prefix-consumption theorem. |
| Anchored seam/exit strategic decoder | `I` | Open. |
| Full-rate stationary cap | `M+L+C` | Landed verifier for supplied profiles. |
| Two-player all-table uniform-payoff existence | `M+L+C` | Unconditional capstone landed in `UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean`; it does not claim stationary exact equilibrium or generalize the pair-repair classification to `n ≥ 3`. |
| Three-player all-table uniform-payoff existence | `M+L+A+C` | Unconditional capstone in `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`; analytic endpoint classification produces a normalized singleton source, and a dimension-three complementary-or-directed-cycle alternative closes it. |
| Sure-exit-set exact characterization (all `n`) | `M+L` | Landed (`QuittingSureExitSet`, `97b77b6`); coalition-face per-phase criterion is now a theorem; two-player joint exit recovered as instance. |
| Two-blocker interval-cover gate | `M+L` | Landed (`QuittingBlockerIntervalCover`, `97b77b6`); single-blocker designation refuted by table witness; with ≤ 2 opponents the switching branch is vacuous, so `n = 3` is the exact threshold. |
| Switching-residue regression and scalar obstructions | `M+L` | Landed (`QuittingSwitchingResidueRegression`, `97b77b6`); the fixed-blocker weight-level branch map is provably not total. |
| Collision-repair exact characterization (owner indifference, spectator no-join, blocker-floor balance) | `M+L` | Landed (`QuittingCollisionRepairCharacterization`, `34fdc11`): full iff, both legs, arbitrary `n` with every non-owner non-blocker a spectator; forced rate δ ≥ γ/(γ+p); sub-floor mechanism failure below γ/(4M); at rate 1 collapses to the sure-exit test. |
| Stationary min-max: `χ = inf_y Φ(y)`, both legs, full history-dependent generality | `M+L` | Landed (`QuittingStationaryMinMax`, `0829959`); constant-row cap supplies phase-switch hypothesis (P) at `punishCap = Φ(y)`; solo-clipped ceiling proved STRICTLY loose (`χ = 0` vs ceiling `2` witness); attainment and the finite-horizon `punishmentLevel` bridge deliberately unclaimed. |
| Shared-punishment price | `M+L` | Two-player shared excess is zero.  A cyclic three-player table has exact behavioral and stationary shared excess `3/4`, with all minimizers classified by a fair first row; on the full-exposure dice table Never is an exact best reply against every committed plan. |
| Budget-to-go, bounded potentials, and charged-path selection | `M+L` | Abstract strong duality and the Bellman least-supersolution are exact. Finite-path capacity, charge on one infinite path, divergence-preserving block selection, renewal, and dependent-choice chronological execution are separated explicitly; for finite edge types the at-most-horizon maximum is attained by a literal path. Delayed-charge, greedy, incompatible-horizon, finite-tower, continuity, and positive-cycle regressions fence off invalid compactness and selection shortcuts. |
| `SwitchRepair` two-scale producer (switching cover → relaxed orbit) | `M [reported]`, REFUTED | Q166 answer: the no-resurrection theorem — occupation charge enters no pointwise packet clause, so vanishing-error packet families (rates bounded below) reduce to exact one-stage repairs or sure-pair sets; the producer cannot exist in the sure-blocker grammar. |
| Two-owner root (support-enlarged one-stage mechanism: sure blocker, both others mix) | `M+L` on the regression; `M [reported]` in general | The explicit enlarged root `(1/2, 1, 1/3)` is a machine-checked exact stationary uniform certificate.  The fully general iff with floors remains mathematical rather than production Lean. |
| K4 regression exact resolution (`χ = (2/3, 0, 2/7)`, period-one orbit `(1, 2/7, 1)`) | `M+L+C` | The two-sure-quitter root and the support-enlarged root are exact stationary uniform certificates with distinct payoffs; the table was never an engine obstruction. |
| Local three-player mechanism residue | `M+L+C` | The locally blocked class is nonempty: a rational parametric family defeats every owner-rate, sure-exit, collision-repair, and interior two-owner/one-sure-blocker cell.  Every member is nevertheless absorbed by an exact omitted double-sure-quitter/mixer root, locating the defect in the local branch grammar. |

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
