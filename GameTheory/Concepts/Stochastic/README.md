# Stochastic games: the uniform-equilibrium program

This directory holds the formalization effort around the **uniform equilibrium
existence problem** — the central open problem of stochastic game theory: every
stochastic game with finitely many players, states, and actions admits a uniform
equilibrium payoff from every initial state.

The conjecture is stated in [`Uniform.lean`](Uniform.lean) as
`StochasticGame.exists_uniformDeviationCapConstructor` and carries the repository's
**only intentional `sorry`** (enforced by `scripts/check_lean_placeholders.py`).
Everything else in this directory is sorry-free; keeper capstones are additionally
axiom-audited (`propext`, `Classical.choice`, `Quot.sound` only).

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
that supplied architecture.  The sharp `11/7` finite-horizon modulus and the
necessity, phase-minimality, and rigidity results studied in Question 97 are
not formalized in that module.

`FTVCyclicMinimality.lean` supplies Question 97's exact finite-algebra layer.
For any live cyclic packet satisfying the table-expanded `(Q1)--(Q5)`
conditions with initial promise `(1,2,1)`, it derives the exposed solo-outcome
face, a unique active role in every phase, coverage of all three roles, the
lower bound `K ≥ 3`, and literal uniqueness of the normalized three-phase
packet.  It also constructs that packet and checks all conditions, including
the inactive complementarity inequalities.  The module does not formalize
the equilibrium-theoretic necessity/sufficiency of `(Q1)--(Q5)`, the sharp
finite-horizon modulus, or Question 97's approximate-regret boundary.

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

### Proved results (special cases of the conjecture)

| Game class | Theorem | File |
|---|---|---|
| Absorbing initial state | `exists_uniformEquilibriumPayoff_of_isAbsorbingState` | `Absorbing.lean` |
| Single-state games | `exists_uniformEquilibriumPayoff_of_subsingleton_state` | `Absorbing.lean` |
| Action-independent transitions (full generality, incl. reducible/periodic) | `exists_uniformEquilibriumPayoff_of_isActionIndependent` | `TransitionIndependent.lean` |
| All children absorbing after one step | `exists_uniformEquilibriumPayoff_of_absorbingChildren` | `OneStepAbsorbingChildUniform.lean` |
| Zero-sum single-controller (from a Vrieze primal optimum) | `exists_uniformEquilibriumPayoff_of_singleController_of_vriezePrimalOptimal` | `SingleControllerFlowReward.lean` |
| **The Big Match** (Blackwell–Ferguson 1968) | `exists_uniformEquilibriumPayoff_live` | `BigMatchUniform.lean` |

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
Thus the single-controller theorem no longer assumes a separately supplied
projection witness.

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
| `Quitting*` | Quitting games (translation lemmas to the uniform concept) |

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
