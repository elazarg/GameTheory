# Stochastic games: the uniform-equilibrium program

This directory holds the formalization effort around the **uniform equilibrium
existence problem** — the central open problem of stochastic game theory: every
stochastic game with finitely many players, states, and actions admits a uniform
equilibrium payoff from every initial state.

There are **two intentional `sorry`s**, and no others:

- `StochasticGame.exists_uniformDeviationCapConstructor` in
  [`UniformExistenceConjecture.lean`](UniformExistenceConjecture.lean) — the
  general problem above, in its quantitative form;
- `quittingGame_exists_uniformEquilibriumPayoff` in
  [`QuittingConjecture.lean`](QuittingConjecture.lean) — the finite-quitting
  case, the program's middle target.

Both are allowlisted by name in `scripts/check_lean_placeholders.py`, which
fails on any third placeholder and equally on an allowlist entry that no longer
carries one — so discharging a conjecture forces the list to be updated.
[`Uniform.lean`](Uniform.lean) holds only the definitions and their proved
equivalence and is itself sorry-free. Everything else in this directory is
sorry-free; keeper capstones are additionally axiom-audited (`propext`,
`Classical.choice`, `Quot.sound` only).

## Payoff terminology used here

Three nearby phrases are not interchangeable in this repository:

- **limiting-average** refers to a payoff defined from the asymptotic Cesaro
  stream, typically through a `liminf`; it is a payoff functional, not by
  itself a uniformity theorem;
- **undiscounted equilibrium payoff** may mean a limit of increasingly
  accurate terminal or asymptotic equilibria; the profile may vary along the
  approximating sequence; and
- **uniform-equilibrium payoff** is the stronger repository predicate: for
  each accuracy, one profile and one fixed target work for every sufficiently
  long finite horizon against every unilateral behavioral deviation.

Never upgrade the first or second notion to the third without a named theorem.
Two valid upgrades currently used here are the positivity/monotonicity argument
for positive recursive absorbing games (Solan--Vieille, Remark 2.9) and the
finite-quitting terminal-to-uniform bridge in
[`QuittingTerminalUniformization.lean`](QuittingTerminalUniformization.lean)
with fixed-payoff selection in
[`QuittingTerminalUniformPayoffSelection.lean`](QuittingTerminalUniformPayoffSelection.lean).

## How this directory is organized

The directory is a **research program**, not a conventional library. A small spine
of infrastructure files evolves continuously; around it, a large number of
exploratory probe files record attempted routes as complete, machine-checked
developments. Probes promote their unresolved residue to explicitly *named
hypotheses* (`Has...`/`Is... : Prop`) instead of `sorry`, and candidate interfaces
are stress-tested against falsifier games (the Big Match no-go is the permanent
baseline). Dead routes are killed by *proved* no-go theorems, kept permanently.

### The spine

```
Basic ─→ StageGame ─→ Uniform (the conjecture; both waists)
  │          │
  │          └─→ Discounted ─→ ZeroSum (Shapley) ─→ Fink ─→ FinkLimit …
  │                     │
  └─→ Adaptive ─→ AdaptiveCertificate ─→ PublicPhaseCertificate …
```

- **Construction waist**: `HasUniformDeviationCapConstructor` (`Uniform.lean`) —
  the quantitative form every construction must reach; proved exactly equivalent
  to the semantic uniform-payoff property.
- **Verification waist**: the adaptive certificates (`AdaptiveCertificate.lean`) —
  proof-facing sufficient conditions (submartingale floor / decoupled bound /
  one-sided guarantee + zero-sum wrapper) that compile candidate constructions
  into `IsUniformEquilibriumPayoff`.

### Repeated-game compatibility

`RealizedActionRepeatedAdapter.lean` proves that public repeated play under
realized-action monitoring is exactly the one-state stochastic game whose
actions are the original pure stage strategies and whose stage payoff is the
original expected utility.  It gives inverse history, strategy, and profile
transports; exact projected history laws; commutation with unilateral strategy
replacement; and equality of finite-average payoffs.  Under the standard
finite stage-game hypotheses this yields exact equivalences for finite-horizon
Nash, fixed-profile uniform-ε equilibrium, and the matching payoff-level
uniform-equilibrium predicate.

The payoff-level monitored predicate is stated separately because its profile
may depend on ε, exactly as in `StochasticGame.IsUniformEquilibriumPayoff`.
The older monitored `IsUniformEquilibrium` fixes one profile and requires its
payoffs to converge.  The adapter proves the sound implication from a fixed
profile with its specified limit, but does not claim a converse without an
additional coherent-selection or compactness theorem.

`TransitionMonitoring.lean` identifies the transition coordinate of the
compiled Bellman/Fink row with the deviation signal law of the canonical
one-step public monitor that observes only the successor state.  The identity
is exact for the baseline, pure unilateral deviations, and scalar continuation
scores.  It is a one-step row adapter only: it does not observe the joint
action and does not construct a history monitor, response strategy, punishment,
or credible closer.

### Fixed public response architectures

`PublicResponseCredibilityCriterion.lean` and its support-pruned companion
`ReachablePublicResponseCredibilityCriterion.lean` supply a second
proof-facing route for a **given finite public Markov response architecture**.
Target harmonicity, unilateral target superharmonicity, a neutral-occupation
inequality, and prescribed delivery produce bounded potentials, uniform
`O(1/N)` delivery and deviation caps, rebasing, and an enforcement ledger
consumed by the existing public-response compilers.

`ArbitraryStartPrescribedDeliveryTelescope.lean` and
`ArbitraryStartUnilateralCap.lean` make the sound part of the corrected Q96
domain split explicit.  The first gives exact endpoint telescopes and uniform
`O(1/N)` delivery after rebasing at any node in the declared
prescribed-closed region.  The second gives the corresponding endpoint and
uniform unilateral cap after rebasing at any node in the selected player's
owner-specific arena.  Neither module enlarges those domains to their union or
asserts the Q96 converse, recurrent coverage, necessity, or obstruction
extraction.

`ExplicitDomainGainBiasVerifier.lean` combines those two domain-correct
telescopes behind one shared modulus and feeds the existing enforcement ledger
at prescribed entries, where membership in every owner arena is available.

`SplitDomainGainBiasVerifier.lean` separates Q96's delivery union from its
owner-specific arenas, adapts each half to the existing APIs, reuses the
mean-ergodic and controlled-Farkas bias theorems, and proves exact endpoint and
shared-modulus gain--bias sufficiency without a recurrent-coverage assumption.

`SplitDomainAsymptoticConverse.lean` proves the two target-side converse steps
on those exact domains.  Shifted prescribed Cesaro delivery forces prescribed
target harmonicity on the delivery union, and an eventual vanishing-error cap
for every pure one-step rollout forces target superharmonicity on the selected
owner's arena.  The hypotheses use the iterated finite configuration kernel;
identifying those rollouts with the architecture's history semantics remains a
separate finite-horizon law bridge.

`ResponseArchitectureConfigKernelLaw.lean` supplies the prescribed half of
that bridge: projecting the full prescribed public-history law to the current
controller configuration is exactly iteration of the prescribed configuration
kernel.  Consequently its expected stage payoffs and rebased finite averages
agree with the corresponding configuration-kernel quantities, and ordinary
history-level shifted delivery now implies prescribed target harmonicity.

`ResponseArchitecturePurePrefixLaw.lean` supplies the unilateral half.  It
formalizes the behavior deviation that plays one selected pure row at a
rebased entry and obeys thereafter, identifies its exact configuration law
and finite average, and proves that history-level shifted delivery plus an
eventual vanishing-error unilateral cap implies both target conditions (T0)
and (Ti) on the split delivery and owner domains.

`ResponseArchitectureMarkovDeviationLaw.lean` generalizes that history law
from a pure prefix to every stationary mixed policy on controller
configurations.  The projected history law, calendar rewards, and rebased
finite averages are exactly the induced finite Markov-kernel quantities; this
is the operational bridge used to test invariant unilateral occupations.

`SplitDomainPrescribedBiasConverse.lean` continues the necessity direction.
From shifted prescribed delivery it proves that the restricted Poisson charge
has zero vector Cesaro limit, and therefore synthesizes the prescribed bias
(A2) on the entire delivery union.  Both configuration-kernel and ordinary
history-semantic entry points are provided.

`SplitDomainNeutralOccupationConverse.lean` closes the owner-occupation half.
It disintegrates every balanced owner-local occupation into a stationary mixed
configuration policy, proves that row closure keeps its supported public
histories inside the declared owner arena, and averages the all-start semantic
cap under the invariant source law.  Thus the cap itself implies (N), with no
recurrent-coverage or separate realizability axiom, and shifted delivery plus
shifted caps synthesize both Q96 bias families without assuming (N).

`SplitDomainSemanticCredibilityCharacterization.lean` packages the exact
fixed-class result.  One shared `O(1/T)` prescribed-delivery and unilateral-cap
predicate, quantified over the delivery union and each selected owner's arena,
is equivalent to a nonempty target/gain--bias packet on those same domains.
The equivalence has no recurrent-coverage premise and makes no claim that a
suitable finite architecture exists for an arbitrary game or target.

`UncoveredPrescribedClassCounterexample.lean` is the two-player/two-node Q96
regression: all four target/occupation-side checks pass on their stated
domains, while the escaped prescribed class is outside player one's arena and
has linear positive delivery error, so its Poisson equation is impossible.

`FTVCyclicCredibility.lean` is the actual-data acceptance test for this
route.  It constructs the Flesch--Thuijsman--Vrieze three-player quitting
game, its ten-configuration public controller (three live clock phases and
seven absorbing children), and the complete target assignment.  It proves
all four criterion conditions and compiles them into an enforcement ledger,
a public-phase punishment system, and an adaptive certificate for payoff
`(1,2,1)` at every positive error.  This is a formal sufficiency result for
that supplied architecture.

`FTVCyclicFiniteHorizon.lean` instantiates the arbitrary-start payoff
telescope with the exact FTV delivery bias.  In the repository's
`quittingGame` convention, the live state pays zero on the quitting stage and
the terminal reward begins one stage later.  The resulting coordinatewise
bounds are `16/(7T)`, `22/(7T)`, and `18/(7T)`, hence `22/(7T)` uniformly over
players.  The often quoted `11/(7T)` constant instead corresponds to counting
the terminal reward already on the quitting stage; it is not the modulus of
the current Lean model.

`FTVCyclicMinimality.lean` supplies Question 97's exact finite-algebra layer.
For any live cyclic packet satisfying the table-expanded `(Q1)--(Q5)`
conditions with initial promise `(1,2,1)`, it derives the exposed solo-outcome
face, a unique active role in every phase, coverage of all three roles, the
lower bound `K ≥ 3`, and literal uniqueness of the normalized three-phase
packet.  It also constructs that packet and checks all conditions, including
the inactive complementarity inequalities.  The module does not formalize
the equilibrium-theoretic necessity/sufficiency of `(Q1)--(Q5)` or Question
97's approximate-regret boundary.

`FTVCyclicSemanticBridge.lean` closes the concrete duplication between those
two modules.  It specializes the supplied-architecture semantic
characterization to the total domain of the ten-node FTV controller, giving
all-start prescribed delivery and unilateral behavioral caps with one common
`O(1/T)` remainder.  It also proves that the controller's live quit
probabilities, promise word, and cyclic successor are exactly the data of the
normalized `ExactCyclicPacket`.  It deliberately does not infer an
arbitrary-`K` packet from arbitrary public-controller semantics: that would
require a separate arbitrary-`K` controller constructor and explicit
reachability and reduction conventions.

`ArchitectureCapSeparators.lean` is a regression guard for the cap notion.
It proves on actual finite games that a supplied architecture's exact
unilateral cap can be `1` while the corresponding one-shot opponent minmax is
`0`, and that testing one deviation followed by immediate obedience can miss
a two-step history-dependent strategy whose average payoff converges to `1`.
Thus neither static minmax nor one-stage-deviation-and-return may replace the
complete unilateral behavior-strategy cap in the credibility interface.

This remains a supplied-object route: it does not construct an architecture
from an arbitrary game or target, bound the number of public configurations,
model hidden randomized memory, or establish that finite public architectures
cover all uniform-equilibrium payoffs.  The fixed-class converse is no longer
an open item, however.  The split-domain converse modules above derive the
target, occupation and bias packets from the corresponding all-start history
semantics on the exact delivery union and owner arenas, with no recurrent-
coverage assumption.

The public stopping stack is also no longer limited to fixed-depth splices.
`PublicVariableStoppingAdaptiveDispatcher.lean` composes child systems at a
bounded causal stopping time, while
`PublicVariableStoppingPrefixLawCompiler.lean` derives the prefix laws and an
explicit amortization horizon from pointwise online-switch potentials.  This
is still a verifier/compiler for supplied stopping rules, child families and
local potential data; it is not a constructor of those objects for an
arbitrary stochastic game.

### Quitting-game terminal and root bridges

`QuittingAsymptotic.lean` identifies every fixed behavior profile's limiting
finite-average payoff with its expected terminal reward.  The root modules
make the missing continuation datum explicit: `QuittingRootContinuation.lean`
proves the exact first-stage disintegration, and
`QuittingFirstBranch.lean` proves that a surely absorbing root/continuation
splice is a terminal `ε`-equilibrium exactly when its product root action is
an `ε`-Nash action of the finite root game with the playerwise continuation
best-response suprema.

`QuittingSimpleBranches.lean` gives the sharp all-continue (`Never`) test,
including the value `max 0 qᵢ` against all-continuing opponents.
`QuittingRootPerturbation.lean` proves the one-coordinate `2 M d` payoff and
`4 M d` other-player regret bounds, including the near-sure-quitter
specialization.  `QuittingFiniteHorizonBridge.lean` proves that common
eventual delivery error `d` and deviation-cap error `c` are impossible when
terminal `ε₀`-equilibrium fails and `c + d < ε₀`; only fixed-profile,
fixed-deviation convergence is used.  These files make no proper
absorption-path equivalence or stationary discretization claim.

The diagonal target-tail modules replace a common punishment continuation by
player-indexed closed tails.  `QuittingTargetAnchoredTail.lean` constructs a
tail that is optimal for one target against any stationary opponent row;
`QuittingFiniteEndpointNashBellmanFactory.lean` supplies exact finite prefixes
with an arbitrary bounded endpoint; and the semantic, bound, and selection
modules compile joint prefix survival `J ≤ δ²` into a terminal
`4 M δ`-equilibrium.  The headline theorem in
`QuittingDiagonalTargetTail.lean` is conditional on accuracy-indexed exact
prefixes with small joint survival.  It neither constructs those prefixes nor
claims uniform existence for all quitting games.  Its contrapositive is a
counterexample restriction: any counterexample has a positive accuracy at
which every exact diagonal target-tail candidate fails the required survival
certificate.

The essential-APS modules isolate the one-randomizer singleton-flow stratum.
`QuittingFleschSuccessor.lean` derives its asymmetric successor graph from two
consecutive proper arcs; `QuittingEssentialAPS.lean` distinguishes executable
one-continuation segments from the larger full-convex-hull operator; and
`QuittingEssentialAPSFixedPoint.lean` constructs the carrier-restricted
greatest algebraic fixed family. `QuittingEssentialAPSCycle.lean` proves that
a supplied finite proper cycle lies in that family and compiles its selected
value to a uniform-equilibrium payoff. On a compact functional unique-live,
terminal-free component satisfying finite-window face avoidance, the infinite
path layer constructs coherent execution and qualitative deleted-player
survival decay. Finite adaptive subdivision at each `p_t < 1` and a nonperiodic
Snell supersolution then compile every initial component value to
a uniform-equilibrium payoff. This is not an arbitrary-game coverage theorem:
convexified fixed-point membership alone does not provide the required
component hypotheses, as the zero-mass regression makes explicit.

The boundary-holonomy surface also includes the affine-residual, max-affine
residual, self-similarity, tangent, and realized-tangent modules. Together
they provide exact residual cocycles, iteration/idempotents, self-similarity,
max-plus tangents, realized first-order bounds, and compact coordinate
subsequences. They do not establish realized-image closedness, retain source
paths, produce strategic blocks, or decode a coefficient limit.

### Proved results (special cases of the conjecture)

| Game class | Theorem | File |
|---|---|---|
| Absorbing initial state | `exists_uniformEquilibriumPayoff_of_isAbsorbingState` | `Absorbing.lean` |
| Single-state games | `exists_uniformEquilibriumPayoff_of_subsingleton_state` | `Absorbing.lean` |
| Action-independent transitions (full generality, incl. reducible/periodic) | `exists_uniformEquilibriumPayoff_of_isActionIndependent` | `TransitionIndependent.lean` |
| All children absorbing after one step | `exists_uniformEquilibriumPayoff_of_absorbingChildren` | `OneStepAbsorbingChildUniform.lean` |
| Zero-sum single-controller (full finite generality) | `exists_uniformEquilibriumPayoff_of_isZeroSumBoolGame_of_isSingleController` | `SingleControllerPrimalExistence.lean` |
| **The Big Match** (Blackwell–Ferguson 1968) | `exists_uniformEquilibriumPayoff_live` | `BigMatchUniform.lean` |
| Compact terminal-free unique-live essential-APS component | `quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live` | `QuittingEssentialAPSUniformPayoff.lean` |

`SingleControllerNoTrap.lean` closes the game-specific no-trap part of that
residual: strong complementarity forces every state to reach the positive
dual-occupation support through the pure-controller support graph.
`SingleControllerRankCompletion.lean` then selects least-distance-decreasing
actions off that support and proves reachability under one fixed completed
stationary kernel, ruling out cyclic local choices.
`SingleControllerFlowCompletion.lean` supplies the stronger same-policy route
needed by Vrieze's original dual: it normalizes `z` on positive occupation
support and `yGain` elsewhere, proves closed-core reachability under that
hybrid kernel, and compiles the resulting off-core transience certificate.
`SingleControllerFlowHarmonicity.lean` then combines complementary slackness
off that support with stationary nonnegative drift on it to prove that the
same hybrid kernel makes the encoded gain harmonic.
`SingleControllerFlowReward.lean` proves exact reward--bias compatibility on
the occupation core, solves the arbitrary off-core residual by a killed
Poisson equation, identifies the worst-reward ergodic projection with the
negative encoded gain, and constructs the controller projection witness.
`SingleControllerPrimalExistence.lean` proves feasibility, bounds every
feasible gain through its one-sided average guarantee, invokes finite LP
attainment, and constructs a primal optimum.  Thus the final
single-controller theorem assumes neither an optimal LP point nor a
separately supplied projection witness.

Supporting classical theorems, fully proved: Fink's discounted stationary
equilibria (`exists_isDiscountedStationaryBellmanEq`, `Fink.lean`), Shapley's
discounted zero-sum value with exact discounted Nash profiles
(`shapleyBehaviorProfile_isDiscountedNash`, `ZeroSum.lean`), and a **conditional
Mertens–Neyman theorem** reducing the zero-sum uniform value to two named
hypotheses (`uniformValue_of_rowColumnTrackingCertificates`,
`MertensNeymanCriterion.lean`).

`BigMatchSelfSimilarity.lean` checks the finite structural core of Question 80
Part D.  The legal live cycle `(Continue, Left)` then `(Continue, Right)` has
maximizer payoffs `0` then `1`, total vector payoff exactly twice
`(1/2,-1/2)`, zero target debt, and an endpoint continuation identical to the
root live continuation.  It does not formalize the external universal
finite-public routing-resistance theorem or any atlas-rank conclusion.

`PrivateRecommendationTargetAbsorbingLift.lean` realizes the sharp
strategic-form correlation separator as the stated four-state one-decision
absorbing game. For every arbitrary behavior profile, its actual
finite-horizon average payoff at every positive horizon equals the static
mixed payoff of the independently randomized root action, and root extraction
commutes with unilateral behavioral replacement. Composing this bridge with
the sharp separator proves that the mediated target `(5/7,5/7)` is not an
ordinary uniform-equilibrium payoff of the lift. This is target-specific: the
game has other ordinary uniform targets. The module defines no private device,
autonomous-equilibrium theorem, universal compiler, or target-free
nonexistence result.

### Negative results (no-go keepers)

No-go and counterexample files are first-class results: each kills a specific
route, is machine-checked, and constrains all future interfaces. Load-bearing
ones include:

- `BigMatchNoMarkov.lean` — uniform witnesses must be history-dependent.
- `BigMatchFinkEndpoint.lean` — refutes the calendar-Markov Fink endpoint.
- `BigMatchDeficitIndexNoGo.lean` — the linear running-deficit index is not a
  universal Mertens–Neyman constructor.
- `DiscountBiasNoGo.lean` — unscaled tail variation cannot control the scaled
  discount-bias drift (the mechanism-2/3 boundary).
- `FinkTangentCounterexample.lean`, `FinkSelectionCounterexample.lean` — the
  supported-harmonic-adjustment route is selection-resistant.
- `PureExternalityCycle.lean` — analytic provenance cannot supply the routing
  gluing invariant.
- `UniformNonexistenceCertificate.lean` — quantitative late-horizon and
  quitting-terminal exploitability gaps rule out every uniform-equilibrium
  payoff.

### Family map (file-name prefixes)

| Prefix | Topic |
|---|---|
| `Adaptive*` | History-adaptive potentials and the certificate verification interface |
| `Analytic*` | Analytic-in-discount Bellman germs: hierarchy, endpoints (λ → 0⁺), obstruction coordinates |
| `Bellman*` | Algebraic Bellman varieties, germs, sign cells, curve gates |
| `BigMatch*` | The Big Match worked instance and its no-gos |
| `FiniteBias*` | Finite-bias canonical endpoint alternatives |
| `Fink*` | Discounted stationary equilibria and the vanishing-discount program |
| `MertensNeyman*` | The conditional MN criterion and adaptive account strategies |
| `PlayerNeutral*` / `PlayerOwned*` / `PlayerInvisible*` | Occupation/charge accounts by action orientation (continuation-neutral vs deviator-owned vs invisible) |
| `Prescribed*` / `MovingEndpoint*` / `Endpoint*` | Endpoint-target transport probes |
| `ProcessedHarmonic*` | Harmonic-adjustment response processing |
| `Public*` | Public-history machinery: stopping rules, phase certificates, response architectures and credibility criteria, punishment systems, public coins |
| `Quitting*` | Quitting games: terminal limits, exact root continuation, Never/First tests, perturbation and finite-horizon refutation bridges |

### File status conventions

- **Core**: the spine files above — evolving infrastructure.
- **Results**: the proved special cases and classical theorems in the tables.
- **No-go / counterexample**: permanent negative results (usually named so).
- **Everything else**: exploratory probes — write-once, sorry-free records of
  attempted routes, kept for their named interfaces and falsifiers. A probe
  having no importers does **not** mean it is dead; probes are consumed by the
  research program, not (yet) by other modules.

The detailed research logs, question corpus, and route scoreboard are maintained
outside the repository (untracked `ephemeral/`); this README is the in-tree map.
The generic mathematics developed for the program (couplings, stitched
martingales, hitting-time potentials, closed classes, occupation flows, curve
selection) lives under `Math/Probability/` and `Math/CurveSelection/`.

## Headline markers

A declaration whose docstring contains the token `HEADLINE` is a load-bearing
result of the uniform-equilibrium program, not a helper. Grep for it to find
the current spine:

```
grep -rn "HEADLINE" GameTheory/Concepts/Stochastic/
```

The marker is for searchability. It records three things a reader needs before
citing the declaration: what it is the headline *of*, what it does **not**
cover, and any hypothesis that is known to be non-removable. Add it sparingly —
if everything is marked, nothing is.
